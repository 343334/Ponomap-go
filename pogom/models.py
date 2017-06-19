#!/usr/bin/python
# -*- coding: utf-8 -*-
import logging
import itertools
import calendar
import sys
import gc
import time
import re
from . import cluster
from peewee import SqliteDatabase, InsertQuery, \
    IntegerField, CharField, DoubleField, BooleanField, \
    DateTimeField, fn, DeleteQuery, CompositeKey, FloatField, SQL, TextField, JOIN, RawQuery
from playhouse.flask_utils import FlaskDB
from playhouse.pool import PooledMySQLDatabase
from playhouse.shortcuts import RetryOperationalError, model_to_dict
from playhouse.migrate import migrate, MySQLMigrator, SqliteMigrator
from datetime import datetime, timedelta
from base64 import b64encode
from cachetools import TTLCache
from cachetools import cached
from operator import itemgetter

from . import config
from .utils import get_pokemon_name, get_pokemon_rarity, get_pokemon_types, get_args, \
     get_move_name, get_move_damage, get_move_energy, get_move_type, date_secs, cur_sec, \
     now, hoursecs, secs_between, clock_between, equi_rect_distance, clear_dict_response
from .transform import transform_from_wgs_to_gcj, get_new_coords
from .customLog import printPokemon

log = logging.getLogger(__name__)

args = get_args()
flaskDb = FlaskDB()
cache = TTLCache(maxsize=100, ttl=60 * 5)

db_schema_version = 10


class MyRetryDB(RetryOperationalError, PooledMySQLDatabase):
    pass


def init_database(app, position):
    if args.db_type == 'mysql':
        log.info('Connecting to MySQL database on %s:%i', args.db_host, args.db_port)
        connections = args.db_max_connections
        if not args.only_server:
            if hasattr(args, 'workers') and args.workers > 0:
                connections *= args.workers
        db = MyRetryDB(
            args.db_name,
            user=args.db_user,
            password=args.db_pass,
            host=args.db_host,
            port=args.db_port,
            max_connections=connections,
            stale_timeout=300)
    else:
        log.info('Connecting to local SQLite database')
        db = SqliteDatabase(args.db)

    app.config['DATABASE'] = db
    flaskDb.init_app(app)

    return db


class BaseModel(flaskDb.Model):

    @classmethod
    def get_all(cls):
        results = [m for m in cls.select().dicts()]
        if args.china:
            for result in results:
                result['latitude'], result['longitude'] = \
                    transform_from_wgs_to_gcj(
                        result['latitude'], result['longitude'])
        return results

class Spawnpoints(BaseModel):
    # Separate spawnpoint and pokemon tables so we dont have to look through potentially millions of rows for our TTH
    spawnpoint_id = CharField(primary_key=True)
    latitude = DoubleField()
    longitude = DoubleField()
    area = CharField(index = True)
    disappear_time = IntegerField(index=True)  # Epoch Unix TTH so it's usuable every hour
    last_modified = DateTimeField(index=True)
    appear_time = IntegerField(index=True, default=91)  # default to 1 to be able to scan it every 15 minutes to determine what kind of spawnpoint it is.
    lastpoke = CharField(index = True, max_length=50)
    lastfind = IntegerField(index=True, default=0)
    lastcalc = IntegerField(index=True, default=0)
    valid = IntegerField(index=True, default=0)

    class Meta:
        indexes = ((('latitude', 'longitude'), False),)#link lat & lon to a single key

    @classmethod
    def get_spawnpoints(cls, swLat, swLng, neLat, neLng, timestamp=0, oSwLat=None, oSwLng=None, oNeLat=None, oNeLng=None):
        log.debug('swLat: {}, swLng: {}, neLat: {}, neLng: {}'.format(swLat, swLng, neLat, neLng))
        query = Spawnpoints.select(Spawnpoints.latitude, Spawnpoints.longitude, Spawnpoints.spawnpoint_id, Spawnpoints.disappear_time.alias('time'), Spawnpoints.appear_time)

        if timestamp > 0:
            query = (query
                    .where(((Spawnpoints.last_modified > datetime.utcfromtimestamp(timestamp / 1000))) &
                            ((Spawnpoints.latitude >= swLat) &
                             (Spawnpoints.longitude >= swLng) &
                             (Spawnpoints.latitude <= neLat) &
                             (Spawnpoints.longitude <= neLng))))
        elif oSwLat and oSwLng and oNeLat and oNeLng:
            # Send spawnpoints in view but exclude those within old boundaries. Only send newly uncovered spawnpoints.
            query = (query
                     .where((((Spawnpoints.latitude >= swLat) &
                              (Spawnpoints.longitude >= swLng) &
                              (Spawnpoints.latitude <= neLat) &
                              (Spawnpoints.longitude <= neLng))) &
                            ~((Spawnpoints.latitude >= oSwLat) &
                              (Spawnpoints.longitude >= oSwLng) &
                              (Spawnpoints.latitude <= oNeLat) &
                              (Spawnpoints.longitude <= oNeLng))))
        elif swLat and swLng and neLat and neLng:
            query = (query
                     .where((Spawnpoints.latitude <= neLat) &
                            (Spawnpoints.latitude >= swLat) &
                            (Spawnpoints.longitude >= swLng) &
                            (Spawnpoints.longitude <= neLng)
                            ))
        if args.spawnpoint_scanning and not args.no_server:
            query = (query
                     .where(Spawnpoints.disappear_time.is_null(False)))

        if args.focus_tth:
            query = (query
                     .where(Spawnpoints.valid == 0))

        query = (query
                 .dicts())

        spawnpoints = {}

        for sp in query:
            key = sp['spawnpoint_id']
            if args.spawnpoint_scanning:
                disappear_time = cls.get_spawn_time(sp['time'], sp['appear_time'])

            if key not in spawnpoints:
                spawnpoints[key] = sp

            if 'time' not in spawnpoints[key] and args.spawnpoint_scanning:
                spawnpoints[key]['time'] = disappear_time

        return list(spawnpoints.values())

    @classmethod
    def get_spawn_time(cls, disappear_time, spawn_length=1800):
        return (disappear_time + (3600 - spawn_length)) % 3600  # disappear times = disappear_time + (3600 - spawn_length)
    
    @classmethod
    def delete_spawnpoints(cls, ids):  # for reducing appear time should a spawnpoint not produce a pokemon when expected
        query = (Spawnpoints
                 .delete()
                 .where((Spawnpoints.spawnpoint_id << ids)))
        #log.debug(query)
        query.execute()
        

    @classmethod
    def get_spawnpoints_in_hex(cls, center, steps):

        n, e, s, w = hex_bounds(center, steps)

        query = (Spawnpoints
                 .select(Spawnpoints.latitude.alias('lat'),
                         Spawnpoints.longitude.alias('lng'),
                         Spawnpoints.disappear_time.alias('time'),
                         Spawnpoints.appear_time,
                         Spawnpoints.spawnpoint_id,
                         Spawnpoints.valid
                         ))
        query = (query.where((Spawnpoints.latitude <= n) &
                             (Spawnpoints.latitude >= s) &
                             (Spawnpoints.longitude >= w) &
                             (Spawnpoints.longitude <= e)
                             ))
        if args.spawnpoint_scanning:
            query = (query
                     .where(Spawnpoints.disappear_time.is_null(False)))
        if args.focus_tth:
            query = (query.where(Spawnpoints.valid == 0))

        s = list(query.dicts())

        # The distance between scan circles of radius 70 in a hex is 121.2436
        # steps - 1 to account for the center circle then add 70 for the edge.
        step_distance = ((steps - 1) * 121.2436) + 70
        # Compare spawnpoint list to a circle with radius steps * 120.
        # Uses the direct geopy distance between the center and the spawnpoint.
        filtered = []

        for idx, sp in enumerate(s):
            if equi_rect_distance(center, (sp['lat'], sp['lng'])) <= step_distance:
                filtered.append(s[idx])

        # At this point, 'time' is DISAPPEARANCE time, we're going to morph it to APPEARANCE time.
        if args.spawnpoint_scanning:
            for location in filtered:            
                spawn_length = max((location['valid'] * location['appear_time']), 12 + (args.scan_retries * 10))  # Give it time to scan and retry
                # examples: time    shifted
                #           0       (   0 + 2700) = 2700 % 3600 = 2700 (0th minute to 45th minute, 15 minutes prior to appearance as time wraps around the hour.)
                #           1800    (1800 + 2700) = 4500 % 3600 =  900 (30th minute, moved to arrive at 15th minute.)
                # todo: this DOES NOT ACCOUNT for pokemons that appear sooner and live longer, but you'll _always_ have at least 15 minutes, so it works well enough.
                location['time'] = cls.get_spawn_time(location['time'], spawn_length - args.spawn_delay)

        log.debug('Spawnpoints: {}'.format(len(filtered)))
        if args.sscluster and args.spawnpoint_scanning:
            filtered = cluster.main(filtered)
            log.debug('Clusters: {}'.format(len(filtered)))
        
        return filtered

    @classmethod
    def get_spawnpoint_ids(cls, center):  # for reducing appear time should a spawnpoint not produce a pokemon when expected
        n, e, s, w = hex_bounds(center, 1)

        query = (Spawnpoints
                 .select(Spawnpoints.spawnpoint_id,
                         Spawnpoints.latitude.alias('lat'),
                         Spawnpoints.longitude.alias('lng'))
                 .where((Spawnpoints.latitude <= n) &
                        (Spawnpoints.latitude >= s) &
                        (Spawnpoints.longitude >= w) &
                        (Spawnpoints.longitude <= e)
                        ))

        s = list(query.dicts())

        # The distance between scan circles of radius 70 in a hex is 121.2436
        # steps - 1 to account for the center circle then add 70 for the edge.
        step_distance = 70
        # Compare spawnpoint list to a circle with radius steps * 120.
        # Uses the direct geopy distance between the center and the spawnpoint.
        filtered = []

        for idx, sp in enumerate(s):
            if equi_rect_distance(center, (sp['lat'], sp['lng'])) <= step_distance:
                filtered.append(s[idx])

        return filtered     

class OldPokes(BaseModel):
    # We are base64 encoding the ids delivered by the api,
    # because they are too big for sqlite to handle.
    encounter_id = CharField(primary_key=True, max_length=50)  # We use this to determine uniqueness
    spawnpoint_id = CharField(index=True)  # We need this to be able to link it to the spawnpoint reference
    pokemon_id = IntegerField(index=True)  # Pokemon ID #
    latitude = DoubleField()  # Leaving these so we don't need to modify map.js
    longitude = DoubleField()
    disappear_time = DateTimeField(index=True)  # we Still need to know when this specific pokemon will despawn
    individual_attack = IntegerField(null=True)
    individual_defense = IntegerField(null=True)
    individual_stamina = IntegerField(null=True)
    move_1 = IntegerField(null=True)
    move_2 = IntegerField(null=True)
    gender = IntegerField(null=True)
    last_modified = DateTimeField(null=True, index=True, default=datetime.utcnow)  # When we found the pokemon
    valid = IntegerField(null=True, index=True)

    class Meta:
        indexes = ((('latitude', 'longitude'), False),)


class Pokemon(BaseModel):
    # We are base64 encoding the ids delivered by the api,
    # because they are too big for sqlite to handle.
    encounter_id = CharField(primary_key=True, max_length=50)  # We use this to determine uniqueness
    spawnpoint_id = CharField(index=True)  # We need this to be able to link it to the spawnpoint reference
    pokemon_id = IntegerField(index=True)  # Pokemon ID #
    latitude = DoubleField()  # Leaving these so we don't need to modify map.js
    longitude = DoubleField()
    disappear_time = DateTimeField(index=True)  # we Still need to know when this specific pokemon will despawn
    individual_attack = IntegerField(null=True)
    individual_defense = IntegerField(null=True)
    individual_stamina = IntegerField(null=True)
    move_1 = IntegerField(null=True)
    move_2 = IntegerField(null=True)
    weight = FloatField(null=True)
    height = FloatField(null=True)
    gender = IntegerField(null=True)
    form = IntegerField(null=True)
    last_modified = DateTimeField(null=True, index=True, default=datetime.utcnow)  # When we found the pokemon
    valid = IntegerField(null=True, index=True)
    ghost = IntegerField(null=False, default=0)

    class Meta:
        indexes = ((('latitude', 'longitude'), False),)

    @staticmethod
    def get_active(swLat, swLng, neLat, neLng, timestamp=0, oSwLat=None, oSwLng=None, oNeLat=None, oNeLng=None):
        query = Pokemon.select()
        if not (swLat and swLng and neLat and neLng):
            query = (query
                     .where(Pokemon.disappear_time > datetime.utcnow())
                     .dicts())
        elif timestamp > 0:
            # If timestamp is known only load modified pokemon.
            query = (query
                     .where(((Pokemon.last_modified > datetime.utcfromtimestamp(timestamp / 1000)) &
                             (Pokemon.disappear_time > datetime.utcnow())) &
                            ((Pokemon.latitude >= swLat) &
                             (Pokemon.longitude >= swLng) &
                             (Pokemon.latitude <= neLat) &
                             (Pokemon.longitude <= neLng)))
                     .dicts())
        elif oSwLat and oSwLng and oNeLat and oNeLng:
            # Send Pokemon in view but exclude those within old boundaries. Only send newly uncovered Pokemon.
            query = (query
                     .where(((Pokemon.disappear_time > datetime.utcnow()) &
                            (((Pokemon.latitude >= swLat) &
                              (Pokemon.longitude >= swLng) &
                              (Pokemon.latitude <= neLat) &
                              (Pokemon.longitude <= neLng))) &
                            ~((Pokemon.disappear_time > datetime.utcnow()) &
                              (Pokemon.latitude >= oSwLat) &
                              (Pokemon.longitude >= oSwLng) &
                              (Pokemon.latitude <= oNeLat) &
                              (Pokemon.longitude <= oNeLng))))
                     .dicts())
        else:
            query = (query
                     .where((Pokemon.disappear_time > datetime.utcnow()) &
                            (((Pokemon.latitude >= swLat) &
                              (Pokemon.longitude >= swLng) &
                              (Pokemon.latitude <= neLat) &
                              (Pokemon.longitude <= neLng))))
                     .dicts())

        # Performance: Disable the garbage collector prior to creating a (potentially) large dict with append().
        gc.disable()

        pokemons = []
        for p in query:
            p['pokemon_name'] = get_pokemon_name(p['pokemon_id'])
            p['pokemon_rarity'] = get_pokemon_rarity(p['pokemon_id'])
            p['pokemon_types'] = get_pokemon_types(p['pokemon_id'])
            if args.china:
                p['latitude'], p['longitude'] = \
                    transform_from_wgs_to_gcj(p['latitude'], p['longitude'])
            pokemons.append(p)

        # Re-enable the GC.
        gc.enable()

        return pokemons

    @staticmethod
    def get_active_by_id(ids, swLat, swLng, neLat, neLng):
        if not (swLat and swLng and neLat and neLng):
            query = (Pokemon
                     .select()
                     .where((Pokemon.pokemon_id << ids) &
                            (Pokemon.disappear_time > datetime.utcnow()))
                     .dicts())
        else:
            query = (Pokemon
                     .select()
                     .where((Pokemon.pokemon_id << ids) &
                            (Pokemon.disappear_time > datetime.utcnow()) &
                            (Pokemon.latitude >= swLat) &
                            (Pokemon.longitude >= swLng) &
                            (Pokemon.latitude <= neLat) &
                            (Pokemon.longitude <= neLng))
                     .dicts())

        # Performance: Disable the garbage collector prior to creating a (potentially) large dict with append().
        gc.disable()

        pokemons = []
        for p in query:
            p['pokemon_name'] = get_pokemon_name(p['pokemon_id'])
            p['pokemon_rarity'] = get_pokemon_rarity(p['pokemon_id'])
            p['pokemon_types'] = get_pokemon_types(p['pokemon_id'])
            if args.china:
                p['latitude'], p['longitude'] = \
                    transform_from_wgs_to_gcj(p['latitude'], p['longitude'])
            pokemons.append(p)

        # Re-enable the GC.
        gc.enable()

        return pokemons

    @classmethod
    @cached(cache)
    def get_seen(cls, timediff):
        if timediff:
            timediff = datetime.utcnow() - timediff
        pokemon_count_query = (Pokemon
                               .select(Pokemon.pokemon_id,
                                       fn.COUNT(Pokemon.pokemon_id).alias('count'),
                                       fn.MAX(Pokemon.disappear_time).alias('lastappeared')
                                       )
                               .where(Pokemon.disappear_time > timediff)
                               .group_by(Pokemon.pokemon_id)
                               .alias('counttable')
                               )
        query = (Pokemon
                 .select(Pokemon.pokemon_id,
                         Pokemon.disappear_time,
                         Pokemon.latitude,
                         Pokemon.longitude,
                         pokemon_count_query.c.count)
                 .join(pokemon_count_query, on=(Pokemon.pokemon_id == pokemon_count_query.c.pokemon_id))
                 .distinct()
                 .where(Pokemon.disappear_time == pokemon_count_query.c.lastappeared)
                 .dicts()
                 )

        # Performance: Disable the garbage collector prior to creating a (potentially) large dict with append().
        gc.disable()

        pokemons = []
        total = 0
        for p in query:
            p['pokemon_name'] = get_pokemon_name(p['pokemon_id'])
            pokemons.append(p)
            total += p['count']

        # Re-enable the GC.
        gc.enable()

        return {'pokemon': pokemons, 'total': total}

    @classmethod
    def get_appearances(cls, pokemon_id, timediff):
        '''
        :param pokemon_id: id of pokemon that we need appearances for
        :param timediff: limiting period of the selection
        :return: list of  pokemon  appearances over a selected period
        '''
        if timediff:
            timediff = datetime.utcnow() - timediff
        query = (Pokemon
                 .select(Pokemon.latitude, Pokemon.longitude, Pokemon.pokemon_id, fn.Count(Pokemon.spawnpoint_id).alias('count'), Pokemon.spawnpoint_id)
                 .where((Pokemon.pokemon_id == pokemon_id) &
                        (Pokemon.disappear_time > timediff)
                        )
                 .group_by(Pokemon.latitude, Pokemon.longitude, Pokemon.pokemon_id, Pokemon.spawnpoint_id)
                 .dicts()
                 )

        return list(query)

    @classmethod
    def get_appearances_times_by_spawnpoint(cls, pokemon_id, spawnpoint_id, timediff):
        '''
        :param pokemon_id: id of pokemon that we need appearances times for
        :param spawnpoint_id: spawnpoing id we need appearances times for
        :param timediff: limiting period of the selection
        :return: list of time appearances over a selected period
        '''
        if timediff:
            timediff = datetime.utcnow() - timediff
        query = (Pokemon
                 .select(Pokemon.disappear_time)
                 .where((Pokemon.pokemon_id == pokemon_id) &
                        (Pokemon.spawnpoint_id == spawnpoint_id) &
                        (Pokemon.disappear_time > timediff)
                        )
                 .order_by(Pokemon.disappear_time.asc())
                 .tuples()
                 )

        return list(itertools.chain(*query))

    @classmethod
    def get_spawn_time(cls, disappear_time):
        return (disappear_time + 2700) % 3600

    @classmethod
    def get_spawnpoints(cls, swLat, swLng, neLat, neLng, timestamp=0, oSwLat=None, oSwLng=None, oNeLat=None, oNeLng=None):
        query = Pokemon.select(Pokemon.latitude, Pokemon.longitude, Pokemon.spawnpoint_id, ((Pokemon.disappear_time.minute * 60) + Pokemon.disappear_time.second).alias('time'), fn.Count(Pokemon.spawnpoint_id).alias('count'))

        if timestamp > 0:
            query = (query
                     .where(((Pokemon.last_modified > datetime.utcfromtimestamp(timestamp / 1000))) &
                            ((Pokemon.latitude >= swLat) &
                             (Pokemon.longitude >= swLng) &
                             (Pokemon.latitude <= neLat) &
                             (Pokemon.longitude <= neLng)))
                     .dicts())
        elif oSwLat and oSwLng and oNeLat and oNeLng:
            # Send spawnpoints in view but exclude those within old boundaries. Only send newly uncovered spawnpoints.
            query = (query
                     .where((((Pokemon.latitude >= swLat) &
                              (Pokemon.longitude >= swLng) &
                              (Pokemon.latitude <= neLat) &
                              (Pokemon.longitude <= neLng))) &
                            ~((Pokemon.latitude >= oSwLat) &
                              (Pokemon.longitude >= oSwLng) &
                              (Pokemon.latitude <= oNeLat) &
                              (Pokemon.longitude <= oNeLng)))
                     .dicts())
        elif swLat and swLng and neLat and neLng:
            query = (query
                     .where((Pokemon.latitude <= neLat) &
                            (Pokemon.latitude >= swLat) &
                            (Pokemon.longitude >= swLng) &
                            (Pokemon.longitude <= neLng)
                            ))

        query = query.group_by(Pokemon.latitude, Pokemon.longitude, Pokemon.spawnpoint_id, SQL('time'))

        queryDict = query.dicts()
        spawnpoints = {}

        for sp in queryDict:
            key = sp['spawnpoint_id']
            disappear_time = cls.get_spawn_time(sp.pop('time'))
            count = int(sp['count'])

            if key not in spawnpoints:
                spawnpoints[key] = sp
            else:
                spawnpoints[key]['special'] = True

            if 'time' not in spawnpoints[key] or count >= spawnpoints[key]['count']:
                spawnpoints[key]['time'] = disappear_time
                spawnpoints[key]['count'] = count

        for sp in list(spawnpoints.values()):
            del sp['count']

        return list(spawnpoints.values())

    @classmethod
    def get_spawnpoints_in_hex(cls, center, steps):
        return Spawnpoints.get_spawnpoints_in_hex(cls, center, steps)


class Pokestop(BaseModel):
    pokestop_id = CharField(primary_key=True, max_length=50)
    enabled = BooleanField()
    latitude = DoubleField()
    longitude = DoubleField()
    last_modified = DateTimeField(index=True)
    lure_expiration = DateTimeField(null=True, index=True)
    active_fort_modifier = CharField(max_length=50, null=True)
    last_updated = DateTimeField(null=True, index=True, default=datetime.utcnow)

    class Meta:
        indexes = ((('latitude', 'longitude'), False),)

    @staticmethod
    def get_stops(swLat, swLng, neLat, neLng, timestamp=0, oSwLat=None, oSwLng=None, oNeLat=None, oNeLng=None, lured=False):

        query = Pokestop.select(Pokestop.active_fort_modifier, Pokestop.enabled, Pokestop.latitude, Pokestop.longitude, Pokestop.last_modified, Pokestop.lure_expiration, Pokestop.pokestop_id)

        if not (swLat and swLng and neLat and neLng):
            query = (query
                     .dicts())
        elif timestamp > 0:
            query = (query
                     .where(((Pokestop.last_updated > datetime.utcfromtimestamp(timestamp / 1000))) &
                            (Pokestop.latitude >= swLat) &
                            (Pokestop.longitude >= swLng) &
                            (Pokestop.latitude <= neLat) &
                            (Pokestop.longitude <= neLng))
                     .dicts())
        elif oSwLat and oSwLng and oNeLat and oNeLng and lured:
            query = (query
                     .where((((Pokestop.latitude >= swLat) &
                              (Pokestop.longitude >= swLng) &
                              (Pokestop.latitude <= neLat) &
                              (Pokestop.longitude <= neLng)) &
                             (Pokestop.active_fort_modifier.is_null(False))) &
                            ~((Pokestop.latitude >= oSwLat) &
                              (Pokestop.longitude >= oSwLng) &
                              (Pokestop.latitude <= oNeLat) &
                              (Pokestop.longitude <= oNeLng)) &
                             (Pokestop.active_fort_modifier.is_null(False)))
                     .dicts())
        elif oSwLat and oSwLng and oNeLat and oNeLng:
            # Send stops in view but exclude those within old boundaries. Only send newly uncovered stops.
            query = (query
                     .where(((Pokestop.latitude >= swLat) &
                             (Pokestop.longitude >= swLng) &
                             (Pokestop.latitude <= neLat) &
                             (Pokestop.longitude <= neLng)) &
                            ~((Pokestop.latitude >= oSwLat) &
                              (Pokestop.longitude >= oSwLng) &
                              (Pokestop.latitude <= oNeLat) &
                              (Pokestop.longitude <= oNeLng)))
                     .dicts())
        elif lured:
            query = (query
                     .where(((Pokestop.last_updated > datetime.utcfromtimestamp(timestamp / 1000))) &
                            ((Pokestop.latitude >= swLat) &
                             (Pokestop.longitude >= swLng) &
                             (Pokestop.latitude <= neLat) &
                             (Pokestop.longitude <= neLng)) &
                            (Pokestop.active_fort_modifier.is_null(False)))
                     .dicts())

        else:
            query = (query
                     .where((Pokestop.latitude >= swLat) &
                            (Pokestop.longitude >= swLng) &
                            (Pokestop.latitude <= neLat) &
                            (Pokestop.longitude <= neLng))
                     .dicts())

        # Performance: Disable the garbage collector prior to creating a (potentially) large dict with append().
        gc.disable()

        pokestops = []
        for p in query:
            if args.china:
                p['latitude'], p['longitude'] = \
                    transform_from_wgs_to_gcj(p['latitude'], p['longitude'])
            pokestops.append(p)

        # Re-enable the GC.
        gc.enable()

        return pokestops

    @classmethod
    def get_stops_in_hex(cls, center, steps):

        n, e, s, w = hex_bounds(center, steps)

        query = (Pokestop
                 .select(Pokestop.latitude.alias('lat'),
                         Pokestop.longitude.alias('lng'),
                         Pokestop.pokestop_id,
                         ))
        query = (query.where((Pokestop.latitude <= n) &
                             (Pokestop.latitude >= s) &
                             (Pokestop.longitude >= w) &
                             (Pokestop.longitude <= e)
                             ))

        s = list(query.dicts())

        circle = get_circle(450, steps)
        filtered = []

        for idx, sp in enumerate(s):
            if equi_rect_distance(center, (sp['lat'], sp['lng'])) <= circle:
                filtered.append(s[idx])
        
        return filtered


class Gym(BaseModel):
    UNCONTESTED = 0
    TEAM_MYSTIC = 1
    TEAM_VALOR = 2
    TEAM_INSTINCT = 3

    gym_id = CharField(primary_key=True, max_length=50)
    team_id = IntegerField()
    guard_pokemon_id = IntegerField()
    gym_points = IntegerField()
    enabled = BooleanField()
    latitude = DoubleField()
    longitude = DoubleField()
    last_modified = DateTimeField(index=True)
    last_scanned = DateTimeField(default=datetime.utcnow)

    class Meta:
        indexes = ((('latitude', 'longitude'), False),)

    @staticmethod
    def get_quick(swLat, swLng, neLat, neLng):

        query = Gym.select(Gym.enabled, Gym.latitude, Gym.longitude, Gym.last_modified, Gym.gym_id)

        query = (query
                 .where((Gym.latitude >= swLat) &
                         (Gym.longitude >= swLng) &
                         (Gym.latitude <= neLat) &
                         (Gym.longitude <= neLng))
                 .dicts())

        # Performance: Disable the garbage collector prior to creating a (potentially) large dict with append().
        gc.disable()

        gyms = []
        for p in query:
            gyms.append(p)

        # Re-enable the GC.
        gc.enable()

        return gyms

    @classmethod
    def get_gyms_in_hex(cls, center, steps):

        n, e, s, w = hex_bounds(center, steps)

        query = (Gym
                 .select(Gym.latitude.alias('lat'),
                         Gym.longitude.alias('lng'),
                         Gym.gym_id,
                         ))
        query = (query.where((Gym.latitude <= n) &
                             (Gym.latitude >= s) &
                             (Gym.longitude >= w) &
                             (Gym.longitude <= e)
                             ))

        s = list(query.dicts())

        circle = get_circle(450, steps)
        filtered = []

        for idx, sp in enumerate(s):
            if equi_rect_distance(center, (sp['lat'], sp['lng'])) <= circle:
                filtered.append(s[idx])
        
        return filtered

    @staticmethod
    def get_gyms(swLat, swLng, neLat, neLng, timestamp=0, oSwLat=None, oSwLng=None, oNeLat=None, oNeLng=None):
        if not (swLat and swLng and neLat and neLng):
            results = (Gym
                       .select()
                       .dicts())
        elif timestamp > 0:
            # If timestamp is known only send last scanned Gyms.
            results = (Gym
                       .select()
                       .where(((Gym.last_scanned > datetime.utcfromtimestamp(timestamp / 1000)) &
                              (Gym.latitude >= swLat) &
                              (Gym.longitude >= swLng) &
                              (Gym.latitude <= neLat) &
                              (Gym.longitude <= neLng)))
                       .dicts())
        elif oSwLat and oSwLng and oNeLat and oNeLng:
            # Send gyms in view but exclude those within old boundaries. Only send newly uncovered gyms.
            results = (Gym
                       .select()
                       .where(((Gym.latitude >= swLat) &
                               (Gym.longitude >= swLng) &
                               (Gym.latitude <= neLat) &
                               (Gym.longitude <= neLng)) &
                              ~((Gym.latitude >= oSwLat) &
                                (Gym.longitude >= oSwLng) &
                                (Gym.latitude <= oNeLat) &
                                (Gym.longitude <= oNeLng)))
                       .dicts())

        else:
            results = (Gym
                       .select()
                       .where((Gym.latitude >= swLat) &
                              (Gym.longitude >= swLng) &
                              (Gym.latitude <= neLat) &
                              (Gym.longitude <= neLng))
                       .dicts())

        # Performance: Disable the garbage collector prior to creating a (potentially) large dict with append().
        gc.disable()

        gyms = {}
        gym_ids = []
        for g in results:
            g['name'] = None
            g['pokemon'] = []
            gyms[g['gym_id']] = g
            gym_ids.append(g['gym_id'])

        if len(gym_ids) > 0:
            pokemon = (GymMember
                       .select(
                           GymMember.gym_id,
                           GymPokemon.cp.alias('pokemon_cp'),
                           GymPokemon.pokemon_id,
                           Trainer.name.alias('trainer_name'),
                           Trainer.level.alias('trainer_level'))
                       .join(Gym, on=(GymMember.gym_id == Gym.gym_id))
                       .join(GymPokemon, on=(GymMember.pokemon_uid == GymPokemon.pokemon_uid))
                       .join(Trainer, on=(GymPokemon.trainer_name == Trainer.name))
                       .where(GymMember.gym_id << gym_ids)
                       .where(GymMember.last_scanned > Gym.last_modified)
                       .order_by(GymMember.gym_id, GymPokemon.cp)
                       .dicts())

            for p in pokemon:
                p['pokemon_name'] = get_pokemon_name(p['pokemon_id'])
                gyms[p['gym_id']]['pokemon'].append(p)

            details = (GymDetails
                       .select(
                           GymDetails.gym_id,
                           GymDetails.name)
                       .where(GymDetails.gym_id << gym_ids)
                       .dicts())

            for d in details:
                gyms[d['gym_id']]['name'] = d['name']

        # Re-enable the GC.
        gc.enable()

        return gyms

    @staticmethod
    def get_gym(id):
        result = (Gym
                  .select(Gym.gym_id,
                          Gym.team_id,
                          GymDetails.name,
                          GymDetails.description,
                          Gym.guard_pokemon_id,
                          Gym.gym_points,
                          Gym.latitude,
                          Gym.longitude,
                          Gym.last_modified,
                          Gym.last_scanned)
                  .join(GymDetails, JOIN.LEFT_OUTER, on=(Gym.gym_id == GymDetails.gym_id))
                  .where(Gym.gym_id == id)
                  .dicts()
                  .get())

        result['guard_pokemon_name'] = get_pokemon_name(result['guard_pokemon_id']) if result['guard_pokemon_id'] else ''
        result['pokemon'] = []

        pokemon = (GymMember
                   .select(GymPokemon.cp.alias('pokemon_cp'),
                           GymPokemon.pokemon_id,
                           GymPokemon.pokemon_uid,
                           GymPokemon.move_1,
                           GymPokemon.move_2,
                           GymPokemon.iv_attack,
                           GymPokemon.iv_defense,
                           GymPokemon.iv_stamina,
                           Trainer.name.alias('trainer_name'),
                           Trainer.level.alias('trainer_level'))
                   .join(Gym, on=(GymMember.gym_id == Gym.gym_id))
                   .join(GymPokemon, on=(GymMember.pokemon_uid == GymPokemon.pokemon_uid))
                   .join(Trainer, on=(GymPokemon.trainer_name == Trainer.name))
                   .where(GymMember.gym_id == id)
                   .where(GymMember.last_scanned > Gym.last_modified)
                   .order_by(GymPokemon.cp.desc())
                   .dicts())

        for p in pokemon:
            p['pokemon_name'] = get_pokemon_name(p['pokemon_id'])

            p['move_1_name'] = get_move_name(p['move_1'])
            p['move_1_damage'] = get_move_damage(p['move_1'])
            p['move_1_energy'] = get_move_energy(p['move_1'])
            p['move_1_type'] = get_move_type(p['move_1'])

            p['move_2_name'] = get_move_name(p['move_2'])
            p['move_2_damage'] = get_move_damage(p['move_2'])
            p['move_2_energy'] = get_move_energy(p['move_2'])
            p['move_2_type'] = get_move_type(p['move_2'])

            result['pokemon'].append(p)

        return result


class ScannedLocation(BaseModel):
    latitude = DoubleField()
    longitude = DoubleField()
    last_modified = DateTimeField(index=True, default=datetime.utcnow)

    class Meta:
        primary_key = CompositeKey('latitude', 'longitude')

    @staticmethod
    def get_recent(swLat, swLng, neLat, neLng, timestamp=0, oSwLat=None, oSwLng=None, oNeLat=None, oNeLng=None):
        activeTime = (datetime.utcnow() - timedelta(minutes=15))
        if timestamp > 0:
            query = (ScannedLocation
                     .select()
                     .where(((ScannedLocation.last_modified >= datetime.utcfromtimestamp(timestamp / 1000))) &
                            (ScannedLocation.latitude >= swLat) &
                            (ScannedLocation.longitude >= swLng) &
                            (ScannedLocation.latitude <= neLat) &
                            (ScannedLocation.longitude <= neLng))
                     .dicts())
        elif oSwLat and oSwLng and oNeLat and oNeLng:
            # Send scannedlocations in view but exclude those within old boundaries. Only send newly uncovered scannedlocations.
            query = (ScannedLocation
                     .select()
                     .where((((ScannedLocation.last_modified >= activeTime)) &
                             (ScannedLocation.latitude >= swLat) &
                             (ScannedLocation.longitude >= swLng) &
                             (ScannedLocation.latitude <= neLat) &
                             (ScannedLocation.longitude <= neLng)) &
                            ~(((ScannedLocation.last_modified >= activeTime)) &
                              (ScannedLocation.latitude >= oSwLat) &
                              (ScannedLocation.longitude >= oSwLng) &
                              (ScannedLocation.latitude <= oNeLat) &
                              (ScannedLocation.longitude <= oNeLng)))
                     .dicts())
        else:
            query = (ScannedLocation
                     .select()
                     .where((ScannedLocation.last_modified >= activeTime) &
                            (ScannedLocation.latitude >= swLat) &
                            (ScannedLocation.longitude >= swLng) &
                            (ScannedLocation.latitude <= neLat) &
                            (ScannedLocation.longitude <= neLng))
                     .order_by(ScannedLocation.last_modified.asc())
                     .dicts())

        return list(query)


class UserData(BaseModel):
    username = CharField(primary_key=True, max_length=50)
    pokemon = BooleanField()
    pokestops = BooleanField()
    gyms = BooleanField()
    scanned = BooleanField()
    spawnpoints = BooleanField()
    ranges = BooleanField()
    lat = DoubleField(null=True, index=True)
    lon = DoubleField(null=True, index=True)
    ip = CharField(max_length=25)


class MainWorker(BaseModel):
    worker_name = CharField(primary_key=True, max_length=50)
    message = CharField()
    method = CharField(max_length=50)
    last_modified = DateTimeField(index=True)


class WorkerStatus(BaseModel):
    username = CharField(primary_key=True, max_length=50)
    pword = CharField(null=True)
    worker_name = CharField()
    success = IntegerField(default=0)
    fail = IntegerField(default=0)
    no_items = IntegerField(default=0)
    skip = IntegerField(default=0)
    captcha = IntegerField(default=0)
    last_modified = DateTimeField(index=True)
    lat = DoubleField(null=True, index=True)
    lon = DoubleField(null=True, index=True)
    last_scan = IntegerField(default=0, index=True)
    flag = IntegerField(default=0)
    thread = IntegerField(null=True, index=True)
    # 0 = Unused, 1 = In use, 2 = Failed, 3 = Resting, 4 = Exception, 5 = Ban
    message = CharField(max_length=255)
    
    @classmethod
    def get_active(cls, name=''):

        query = (WorkerStatus
                 .select()
                 .where(WorkerStatus.flag == 1))
        if len(name) > 0:
            query = (query
                     .where(WorkerStatus.worker_name == name))
        query = (query
                 .count())

        return query

    @classmethod
    def populate_db(cls, accounts):
        query = (WorkerStatus
                 .select(WorkerStatus.username)
                 .dicts())
        dbacc = [(p['username']) for p in query]
        del query

        insert = []
        for i in accounts:
            if i['username'] not in dbacc:
                spawninsert = {
                            'username': i['username'],
                            'pword': i['password'],
                            'worker_name': args.status_name,
                            'success': 0,
                            'fail': 0,
                            'no_items': 0,
                            'skip': 0,
                            'captcha': 0,
                            'last_modified': datetime.utcnow(),
                            'lat': None,
                            'lon': None,
                            'last_scan': None,
                            'flag': 0,
                            'message': 'Unused'
                            }
                insert.append(spawninsert)
                log.info('New worker found, adding {} to db'.format(i['username']))
        del dbacc

        if len(insert) > 0:
            WorkerStatus.insert_many(insert).execute()

    @staticmethod
    def get_recent():
        query = (WorkerStatus
                 .select()
                 .where((WorkerStatus.last_modified >=
                        (datetime.utcnow() - timedelta(minutes=5))))
                 .dicts())

        status = []
        for s in query:
            status.append(s)

        return status

    @classmethod
    def get_unused_accounts(cls):
        query = (WorkerStatus
                 .select()
                 .where(WorkerStatus.flag < 1)
                 .count())
        return query

    @classmethod
    def get_held_accounts(cls):
        query = (WorkerStatus
                 .select()
                 .where(WorkerStatus.flag > 1)
                 .count())
        return query


    # If we only need a single, closest account
    @classmethod
    def get_closest_available(cls, latitude, longitude, wid):
        log.debug('Grabbing worker from database')
        
        query = RawQuery(WorkerStatus, "update workerstatus set thread=" + str(wid) + ", last_modified = UTC_TIMESTAMP, flag=1, worker_name='" + args.status_name + "' where (flag = 0) or (worker_name='" + args.status_name + "' and flag = 1 and thread=" + str(wid) + ") order by flag desc, (((6371 * acos(cos(radians(" + str(latitude) + ")) * cos(radians(lat)) * cos(radians(lon) - radians(" + str(longitude) + ")) + sin(radians(" + str(latitude) + ")) * sin(radians(lat)))) * 1000) / (UNIX_TIMESTAMP(UTC_TIMESTAMP) - last_scan)) asc limit 1;").execute()
        
        query = (WorkerStatus
                 .select()
                 .where(WorkerStatus.flag == 1, WorkerStatus.worker_name == args.status_name, WorkerStatus.thread == wid)
                 .order_by(WorkerStatus.last_modified.desc())
                 .limit(1)
                 .dicts())

        db = list(query.dicts())
        acc = db[0]
        acc['auth_service'], acc['pass'] = 'ptc', acc['pword']
        # use the worker that would be able to arrive with the lowest speed.
        log.debug('Worker selected: {}'.format(acc))

        return acc if acc else WorkerStatus.populate_db(args.accounts)


def get_speed(distance, time):
    # v = distance / time
    # time is in seconds, distance is in meters, giving us meters/sec
    time = max(time, 1)  # Time needs to be at least 1 second
    return (distance / time)


class Versions(flaskDb.Model):
    key = CharField()
    val = IntegerField()

    class Meta:
        primary_key = False


class GymMember(BaseModel):
    gym_id = CharField(index=True)
    pokemon_uid = CharField()
    last_scanned = DateTimeField(default=datetime.utcnow)

    class Meta:
        primary_key = False


class GymPokemon(BaseModel):
    pokemon_uid = CharField(primary_key=True, max_length=50)
    pokemon_id = IntegerField()
    cp = IntegerField()
    trainer_name = CharField()
    num_upgrades = IntegerField(null=True)
    move_1 = IntegerField(null=True)
    move_2 = IntegerField(null=True)
    height = FloatField(null=True)
    weight = FloatField(null=True)
    stamina = IntegerField(null=True)
    stamina_max = IntegerField(null=True)
    cp_multiplier = FloatField(null=True)
    additional_cp_multiplier = FloatField(null=True)
    iv_defense = IntegerField(null=True)
    iv_stamina = IntegerField(null=True)
    iv_attack = IntegerField(null=True)
    last_seen = DateTimeField(default=datetime.utcnow)


class Trainer(BaseModel):
    name = CharField(primary_key=True, max_length=50)
    team = IntegerField()
    level = IntegerField()
    last_seen = DateTimeField(default=datetime.utcnow)


class GymDetails(BaseModel):
    gym_id = CharField(primary_key=True, max_length=50)
    name = CharField()
    description = TextField(null=True, default="")
    url = CharField()
    last_scanned = DateTimeField(default=datetime.utcnow)


class HashKeys(BaseModel):
    key = CharField(primary_key=True, max_length=20)
    maximum = IntegerField(default=0)
    remaining = IntegerField(default=0)
    peak = IntegerField(default=0)
    expires = DateTimeField(null=True)
    last_updated = DateTimeField(default=datetime.utcnow)

    @staticmethod
    def get_by_key(key):
        query = (HashKeys
                 .select()
                 .where(HashKeys.key == key)
                 .dicts())

        return query[0] if query else {
            'maximum': 0,
            'remaining': 0,
            'peak': 0,
            'expires': None,
            'last_updated': None
        }

    @staticmethod
    def get_obfuscated_keys():
        hashkeys = HashKeys.get_all()
        for i, s in enumerate(hashkeys):
            hashkeys[i]['key'] = s['key'][:-9] + '*'*9
        return hashkeys


    @classmethod
    def populate_db(cls, keys):
        query = (HashKeys
                 .select(HashKeys.key)
                 .dicts())
        dbkeys = [(p['key']) for p in query]

        insert = []
        for i in keys:
            if i not in dbkeys:
                api.activate_hash_server(key)
                keymax = HashServer.status.get('maximum')
                expires = HashServer.status.get('expiration')
                expires = datetime.utcfromtimestamp(int(expires))

                from_zone = tz.tzutc()
                to_zone = tz.tzlocal()

                expires = expires.replace(tzinfo=from_zone)
                expires = expires.astimezone(to_zone)
                expires = expires.strftime('%Y-%m-%d %H:%M:%S')
                keyinsert = {
                            'key': i,
                            'maximum': keymax,
                            'remaining': 0,
                            'peak': 0,
                            'expires': expires,
                            'last_updated': datetime.utcnow()
                            }
                insert.append(keyinsert)
                log.info('New key found, adding {} to db'.format(i))

        if len(insert) > 0:
            HashKeys.insert_many(insert).execute()


def hex_bounds(center, steps, dist=0.07):
    # Make a box that is (70m * step_limit * 2) + 70m away from the center point.
    # Rationale is that you need to travel.
    sp_dist = dist * 2 * steps
    n = get_new_coords(center, sp_dist, 0)[0]
    e = get_new_coords(center, sp_dist, 90)[1]
    s = get_new_coords(center, sp_dist, 180)[0]
    w = get_new_coords(center, sp_dist, 270)[1]
    return (n, e, s, w)


def construct_pokemon_dict(pokemons, p, encounter_result, d_t, nptime, validx):
    pokemons[p['encounter_id']] = {
        'encounter_id': b64encode(str(p['encounter_id'])),
        'spawnpoint_id': p['spawn_point_id'],
        'pokemon_id': p['pokemon_data']['pokemon_id'],
        'latitude': p['latitude'],
        'longitude': p['longitude'],
        'disappear_time': d_t,
        'last_modified': nptime,
        'valid': validx,
    }
    log.debug(pokemons)
    if encounter_result is not None and 'wild_pokemon' in encounter_result['responses']['ENCOUNTER']:
        pokemon_info = encounter_result['responses']['ENCOUNTER']['wild_pokemon']['pokemon_data']
        attack = pokemon_info.get('individual_attack', 0)
        defense = pokemon_info.get('individual_defense', 0)
        stamina = pokemon_info.get('individual_stamina', 0)
        pokemons[p['encounter_id']].update({
            'individual_attack': attack,
            'individual_defense': defense,
            'individual_stamina': stamina,
            'move_1': pokemon_info['move_1'],
            'move_2': pokemon_info['move_2'],
            'height': pokemon_info['height_m'],
            'weight': pokemon_info['weight_kg'],
            'gender': pokemon_info['pokemon_display']['gender']
        })

        # Check for Unown's alphabetic character
        if (pokemon_info['pokemon_id'] == 201 and 'form' in pokemon_info['pokemon_display']):
            tempform = pokemon_info['pokemon_display']['form']
        else:
            tempform = None

        pokemons[p['encounter_id']].update({
            'form': tempform
        })
    else:
        if encounter_result is not None and 'wild_pokemon' not in encounter_result['responses']['ENCOUNTER']:
            log.warning("Error encountering {}, status code: {}".format(p['encounter_id'], encounter_result['responses']['ENCOUNTER']['status']))
        pokemons[p['encounter_id']].update({
            'individual_attack': None,
            'individual_defense': None,
            'individual_stamina': None,
            'move_1': None,
            'move_2': None,
            'height': None,
            'weight': None,
            'gender': None,
            'form': None
        })


# todo: this probably shouldn't _really_ be in "models" anymore, but w/e ¯\_(ツ)_/¯
def parse_map(args, map_dict, step_location, db_update_queue, wh_update_queue, api, spawns, key_scheduler):
    pokemons = {}
    pokestops = {}
    gyms = {}
    skipped = 0
    stopsskipped = 0
    hashuse = 0
    forts = None
    wild_pokemon = None
    pokesfound = False
    nearbyfound = False
    fortsfound = False
    validcount = 0
    blinded = 0

    cells = map_dict['responses']['GET_MAP_OBJECTS']['map_cells']
    for cell in cells:
        if config['parse_pokemon']:
            if len(cell.get('wild_pokemons', [])) > 0:
                pokesfound = True
                if wild_pokemon is None:
                    wild_pokemon = cell.get('wild_pokemons', [])
                else:
                    wild_pokemon += cell.get('wild_pokemons', [])
            if len(cell.get('nearby_pokemons', [])) > 0:
                nearbyfound = True
                
        if len(cell.get('forts', [])) > 0:  # Why are we only checking this if we're parsing stops and gyms? We need it for error handling!
            fortsfound = True
            if forts is None:
                forts = cell.get('forts', [])
            else:
                forts += cell.get('forts', [])
    del cells

    if pokesfound:
        log.debug('found a pokemon!')
        tempspawn = []
        encounter_ids = [b64encode(str(p['encounter_id'])) for p in wild_pokemon]
        # For all the wild Pokemon we found check if an active Pokemon is in the database.
        query = (Pokemon
                 .select(Pokemon.encounter_id, Pokemon.spawnpoint_id)
                 .where(Pokemon.encounter_id << encounter_ids)
                 .dicts())

        # Store all encounter_ids and spawnpoint_id for the pokemon in query (all thats needed to make sure its unique).
        encountered_pokemon = [(p['encounter_id'], p['spawnpoint_id']) for p in query]

        #for p in wild_pokemon:
            #if (b64encode(str(p['encounter_id'])), p['spawn_point_id']) in encountered_pokemon:
        #dbacc = list(query)
        insert = []

        for p in wild_pokemon:
            tempspawn.append(p['spawn_point_id'])
            #if (b64encode(str(p['encounter_id'])), p['spawn_point_id']) in encountered_pokemon:
                # If pokemon has been encountered before dont process it.
                #if encountered_pokemon['valid'] > 0:  # if we already know the TTH of this pokemon we can safely skip it
                    #skipped += 1
                    #continue

            # time_till_hidden_ms was overflowing causing a negative integer.
            # It was also returning a value above 3.6M ms.
            nptime = p['last_modified_timestamp_ms'] / 1000  # when we spotted the pokemon in unix time
            tth = p['time_till_hidden_ms'] / 1000  # We will only ever get this from a valid pokemon time
            log.debug('niantic discovery time: {}'.format(nptime))
            log.debug('niantic TTH: {}'.format(tth))
            deftime = 90  # Default time given to all invalid pokemon
            log.debug('current hour, in seconds: {}'.format(hoursecs()))
            pokenow = b64encode(str(p['encounter_id']))
            log.debug('current pokemon ID: {}'.format(pokenow))
            log.debug('Spawnpoint_id: {}'.format(p['spawn_point_id']))
            if 0 < tth < 3600:
                log.debug('valid timer found')
                d_t = nptime + tth
                atime = 1800
                try:
                    query = (Spawnpoints
                             .select(Spawnpoints.appear_time, Spawnpoints.valid)  # we just need appearance time, since this got a valid TTH from the server
                             .where(Spawnpoints.spawnpoint_id == p['spawn_point_id']))  # grab matching spawn point
                    x = list(query.dicts())  # cant seem to get the results otherwise
                    db = x[0]  # break the query out of the list
                    atime = max(db['appear_time'], atime)
                    if db['valid'] == 1:  # don't change the disappear time if we already know it.
                        d_t = db['disappear_time'] + hoursecs()
                except:
                    log.debug('got a valid timer the first try!')
                atime = 1800 + (int((db['appear_time'] - 1) / 1800) * 1800)  # keeps or corrects old appearance time now that we have a good TTH
                if atime > 3600:
                    atime = 3600
                valid = 1
            else:
                # lets see if we've got good data from this spawnpoint before.
                log.debug('no valid timer found, checking to see if we have a matching spawnpoint')
                try:
                    query = (Spawnpoints
                             .select(Spawnpoints.disappear_time, Spawnpoints.appear_time, Spawnpoints.valid, Spawnpoints.lastpoke, Spawnpoints.lastfind, Spawnpoints.lastcalc)  # we just need (dis)appearance times and its validity
                             .where(Spawnpoints.spawnpoint_id == p['spawn_point_id']))  # grab matching spawn point
                    x = list(query.dicts())  # cant seem to get the results otherwise
                    db = x[0]  # break the query out of the list

                    # Now for the rules:
                    # 1. don't touch valid TTH times EVAR
                    # 2. we only know that we have at least 90 seconds left from an invalid scan
                    # 3. New pokemon less than an hour later > new spawn time equal to now
                    # 4. Same pokemon since last scan > new TTH time = now + 90 seconds
                    log.debug('last TTH: {}'.format(db['disappear_time']))
                    d_t = db['lastcalc']  # we found this point before and assigned it a disappear time, but did we already calc it for next hour?
                    # Don't calculate with an old time
                    atime = db['appear_time']
                    sptime = d_t - atime  # when we expected it to spawn this time
                    log.debug('Current time: {}; found at: {}; expected spawn: {}; expected gone: {}; spawn length: {}'.format(now(), nptime, sptime, d_t, atime))
                    valid = db['valid']
                    # Finished calculating all our values to compare with

                    if (pokenow == db['lastpoke']) and (nptime + deftime > d_t) and (valid < 1):
                        # If the pokemon is the same as last one, then it's been less than an hour
                        # We're looking for a new TTH
                        d_t = nptime + deftime
                        atime = d_t - sptime
                    elif (pokenow != db['lastpoke']) and (valid == 1 or 0 < nptime - d_t < (3600 - deftime)):
                        # New pokemon, and either a valid disappear time or less than an hour since the last one
                        # We're looking for a new spawn length
                        if valid == 1:
                            while d_t < nptime:  # bring d_t to current hour
                                d_t += 3600
                            sptime = d_t - atime
                        elif valid == 0:
                            d_t += 3600
                            sptime = d_t - atime
                        if nptime < sptime:
                            sptime = nptime
                            atime = max(atime, (d_t - sptime))  # if we already have a longer spawn length
                            if atime < 0 or atime > 3600:
                                atime = deftime  # Who ya gunna call?

                    log.debug('adjusted: disappear {}, spawn {}, spawn length {}'.format(d_t, sptime, atime))
                    if atime > 3600:
                        atime = 3600
                    elif atime < 0:
                        atime += 3600

                    if valid == 1:  # If we have a valid tth, then we can calculate Hx15 length
                        atime = 1800 + (int((db['appear_time'] - 1) / 1800) * 1800)  # keeps or corrects old appearance time now that we have a good TTH

                    log.debug('valid: {}'.format(valid))
                except:
                    log.debug('nope, gotta assume then')
                    atime = deftime
                    d_t = nptime + atime  # since 90 seconds is all we can guarantee
                    log.info('new spawnpoint found, assuming 91 seconds')
                    valid = 0

            log.debug('atime: {}'.format(atime))
            dtsecs = d_t % 3600
            log.debug('d_t: {}'.format(d_t))
            log.debug('dtsecs: {}'.format(dtsecs))
            spawninsert = {
                    'spawnpoint_id': p['spawn_point_id'],
                    'latitude': p['latitude'],
                    'longitude': p['longitude'],
                    'area': args.status_name,
                    'disappear_time': dtsecs,
                    'last_modified': datetime.utcfromtimestamp(now()),
                    'appear_time': atime,
                    'lastpoke': pokenow,
                    'lastfind': nptime,
                    'lastcalc': d_t,
                    'valid': valid
                    }
            InsertQuery(Spawnpoints, spawninsert).upsert().execute()

            log.debug('sweet, so we calculated the new pokemon times')
            log.debug(datetime.utcnow())
            d_t = datetime.utcfromtimestamp(d_t)  # convert our unix time to a datetime for use in the pokemon table
            log.debug(d_t)
            nptime = datetime.utcfromtimestamp(nptime)
            log.debug(nptime)

            printPokemon(p['pokemon_data']['pokemon_id'], p['latitude'],
                         p['longitude'], d_t)

            # Scan for IVs and moves.
            encounter_result = None
            if (args.encounter and (p['pokemon_data']['pokemon_id'] in args.encounter_whitelist or
                                    p['pokemon_data']['pokemon_id'] not in args.encounter_blacklist and not args.encounter_whitelist)):
                time.sleep(args.encounter_delay)
                # Set up encounter request envelope
                if args.hash_key:
                    key = next(key_scheduler)
                    log.debug('Using key {} for this scan.'.format(key))
                    api.activate_hash_server(key)
                req = api.create_request()
                encounter_result = req.encounter(encounter_id=p['encounter_id'],
                                                 spawn_point_id=p['spawn_point_id'],
                                                 player_latitude=step_location[0],
                                                 player_longitude=step_location[1])
                req.check_challenge()
                req.get_hatched_eggs()
                req.get_inventory()
                req.check_awarded_badges()
                req.download_settings()
                req.get_buddy_walked()
                encounter_result = req.call()
                encounter_result = clear_dict_response(encounter_result)
                hashuse += 1
                #HashKeys.addone(key)
            if p['pokemon_data']['pokemon_id'] not in args.ignore_list:
                log.debug('creating dict, valid = {}'.format(valid))
                construct_pokemon_dict(pokemons, p, encounter_result, d_t, nptime, valid)
                log.debug('dict made')
                # Parse only if Pokemon not in Ignore list
                pokemons[p['encounter_id']] = {
                    'encounter_id': b64encode(str(p['encounter_id'])),
                    'spawnpoint_id': p['spawn_point_id'],
                    'pokemon_id': p['pokemon_data']['pokemon_id'],
                    'latitude': p['latitude'],
                    'longitude': p['longitude'],
                    'disappear_time': d_t,
                    'last_modified': nptime,
                    'individual_attack': pokemons[p['encounter_id']]['individual_attack'],
                    'individual_defense': pokemons[p['encounter_id']]['individual_defense'],
                    'individual_stamina': pokemons[p['encounter_id']]['individual_stamina'],
                    'move_1': pokemons[p['encounter_id']]['move_1'],
                    'move_2': pokemons[p['encounter_id']]['move_2'],
                    'valid': valid,
                    'height': pokemons[p['encounter_id']]['height'],
                    'weight': pokemons[p['encounter_id']]['weight'],
                    'gender': pokemons[p['encounter_id']]['gender'],
                    'form': pokemons[p['encounter_id']]['form']
                }

                if args.webhooks:
                    wh_update_queue.put(('pokemon', {
                        'encounter_id': b64encode(str(p['encounter_id'])),
                        'spawnpoint_id': p['spawn_point_id'],
                        'pokemon_id': p['pokemon_data']['pokemon_id'],
                        'latitude': p['latitude'],
                        'longitude': p['longitude'],
                        'disappear_time': calendar.timegm(d_t.timetuple()),
                        'last_modified_time': p['last_modified_timestamp_ms'],
                        'time_until_hidden_ms': p['time_till_hidden_ms']
                    }))
            else:
                log.debug('Pokemon in ignore list, updated spawnpoint, skipped upserting pokemon')
        log.debug('pokemon loop finished')

        # By this point we know what pokemon we found and what pokemon are around, So to check for shadowban we need a list of pokemon we CANT see
        # When we finish parsing the pokemon here, check the pokemon within scan range to see if we have a pre-existing rare pokemon already spawned that we didn't see.
        # If we find one, good, we're not blinded. If we don't and there's one within direct scan range, we're blinded. Otherwise check the nearby list for rares
        # After X scans where neither primary nor nearby scans come up with no rares, we swap it out with flag 6 (blind) similar to max_empties and max_failures

        spawns = checkspawns(spawns, tempspawn)
        if len(spawns) > 0:
            log.debug('spawn points not found: {}'.format(spawns))
#        for i in spawns:
#            query = (Spawnpoints
#                     .select()
#                     .where(Spawnpoints.spawnpoint_id == i)
#                     .dicts())
#            db = list(query)
#            p = db[0]
            # We only got spawnpoints that are within range that should have had pokemon.
#            if p['valid'] > 0:  # we still dont know enough about invalid pokemon to gauge their spawn length when they're not found
#                d_t = p['disappear_time'] + hoursecs()
#                if d_t < now():
#                    d_t += 3600
#                sptime = d_t - atime
            
#                if sptime < now():  # no need to touch spawn length if we already know it shouldn't be here.
#                    sptime = now()
#                    atime = min(d_t - sptime, p['appear_time'])
#                    atime = 900 + (int((db['appear_time'] - 1) / 900) * 900)
#                    query = (Spawnpoints
#                             .update(appear_time=atime, last_modified=datetime.utcfromtimestamp(now()))
#                             .where(Spawnpoints.spawnpoint_id == i))
#                    query.execute()

    if fortsfound:
        if config['parse_pokestops']:
            stop_ids = [f['id'] for f in forts if f.get('type') == 1]
            if len(stop_ids) > 0:
                query = (Pokestop
                         .select(Pokestop.pokestop_id, Pokestop.last_modified)
                         .where((Pokestop.pokestop_id << stop_ids))
                         .dicts())
                encountered_pokestops = [(f['pokestop_id'], int((f['last_modified'] - datetime(1970, 1, 1)).total_seconds())) for f in query]

        for f in forts:
            if config['parse_pokestops'] and f.get('type') == 1:  # Pokestops.
                if 'active_fort_modifier' in f:
                    lure_expiration = datetime.utcfromtimestamp(
                        f['last_modified_timestamp_ms'] / 1000.0) + timedelta(minutes=30)
                    active_fort_modifier = f['active_fort_modifier']
                    if args.webhooks and args.webhook_updates_only:
                        wh_update_queue.put(('pokestop', {
                            'pokestop_id': b64encode(str(f['id'])),
                            'enabled': f['enabled'],
                            'latitude': f['latitude'],
                            'longitude': f['longitude'],
                            'last_modified_time': f['last_modified_timestamp_ms'],
                            'lure_expiration': calendar.timegm(lure_expiration.timetuple()),
                            'active_fort_modifier': active_fort_modifier
                        }))
                else:
                    lure_expiration, active_fort_modifier = None, None

                # Send all pokéstops to webhooks.
                if args.webhooks and not args.webhook_updates_only:
                    # Explicitly set 'webhook_data', in case we want to change the information pushed to webhooks,
                    # similar to above and previous commits.
                    l_e = None

                    if lure_expiration is not None:
                        l_e = calendar.timegm(lure_expiration.timetuple())

                    wh_update_queue.put(('pokestop', {
                        'pokestop_id': b64encode(str(f['id'])),
                        'enabled': f['enabled'],
                        'latitude': f['latitude'],
                        'longitude': f['longitude'],
                        'last_modified': f['last_modified_timestamp_ms'],
                        'lure_expiration': l_e,
                        'active_fort_modifier': active_fort_modifier
                    }))

                if (f['id'], int(f['last_modified_timestamp_ms'] / 1000.0)) in encountered_pokestops:
                    # If pokestop has been encountered before and hasn't changed dont process it.
                    stopsskipped += 1
                    continue

                pokestops[f['id']] = {
                    'pokestop_id': f['id'],
                    'enabled': f['enabled'],
                    'latitude': f['latitude'],
                    'longitude': f['longitude'],
                    'last_modified': datetime.utcfromtimestamp(
                        f['last_modified_timestamp_ms'] / 1000.0),
                    'lure_expiration': lure_expiration,
                    'active_fort_modifier': active_fort_modifier
                }

            elif config['parse_gyms'] and f.get('type') is None:  # Currently, there are only stops and gyms
                # Send gyms to webhooks.
                if args.webhooks and not args.webhook_updates_only:
                    # Explicitly set 'webhook_data', in case we want to change the information pushed to webhooks,
                    # similar to above and previous commits.
                    wh_update_queue.put(('gym', {
                        'gym_id': b64encode(str(f['id'])),
                        'team_id': f.get('owned_by_team', 0),
                        'guard_pokemon_id': f.get('guard_pokemon_id', 0),
                        'gym_points': f.get('gym_points', 0),
                        'enabled': f['enabled'],
                        'latitude': f['latitude'],
                        'longitude': f['longitude'],
                        'last_modified': f['last_modified_timestamp_ms']
                    }))

                gyms[f['id']] = {
                    'gym_id': f['id'],
                    'team_id': f.get('owned_by_team', 0),
                    'guard_pokemon_id': f.get('guard_pokemon_id', 0),
                    'gym_points': f.get('gym_points', 0),
                    'enabled': f['enabled'],
                    'latitude': f['latitude'],
                    'longitude': f['longitude'],
                    'last_modified': datetime.utcfromtimestamp(
                        f['last_modified_timestamp_ms'] / 1000.0),
                }
        del forts

    if len(pokemons):
        log.debug('placing pokemon in update queue')
        db_update_queue.put((Pokemon, pokemons))
    if len(pokestops):
        db_update_queue.put((Pokestop, pokestops))
    if len(gyms):
        db_update_queue.put((Gym, gyms))

    log.info('Parsing found %d pokemons, %d pokestops, and %d gyms.',
             len(pokemons) + skipped,
             len(pokestops) + stopsskipped,
             len(gyms))

    log.debug('Skipped %d Pokemons and %d pokestops.',
              skipped,
              stopsskipped)

    db_update_queue.put((ScannedLocation, {0: {
        'latitude': step_location[0],
        'longitude': step_location[1],
    }}))
    log.debug('all donesies')
    return {
        'count': skipped + stopsskipped + len(pokemons) + len(pokestops) + len(gyms),
        'gyms': gyms,
        'nearby': nearbyfound,
        'nearfort': len(pokestops) + len(gyms),
        'pokes': len(pokemons) - skipped,
        'pokesfound': pokesfound,
        'validcount': validcount,
        'hashuses': hashuse,
        'blind': blinded
    }


def parse_gyms(args, gym_responses, wh_update_queue):
    gym_details = {}
    gym_members = {}
    gym_pokemon = {}
    trainers = {}

    i = 0
    for g in list(gym_responses.values()):
        gym_state = g['gym_state']
        gym_id = gym_state['fort_data']['id']

        gym_details[gym_id] = {
            'gym_id': gym_id,
            'name': g['name'],
            'description': g.get('description'),
            'url': g['urls'][0],
        }

        if args.webhooks:
            webhook_data = {
                'id': gym_id,
                'latitude': gym_state['fort_data']['latitude'],
                'longitude': gym_state['fort_data']['longitude'],
                'team': gym_state['fort_data'].get('owned_by_team', 0),
                'name': g['name'],
                'description': g.get('description'),
                'url': g['urls'][0],
                'pokemon': [],
            }

        for member in gym_state.get('memberships', []):
            gym_members[i] = {
                'gym_id': gym_id,
                'pokemon_uid': member['pokemon_data']['id'],
            }

            gym_pokemon[i] = {
                'pokemon_uid': member['pokemon_data']['id'],
                'pokemon_id': member['pokemon_data']['pokemon_id'],
                'cp': member['pokemon_data']['cp'],
                'trainer_name': member['trainer_public_profile']['name'],
                'num_upgrades': member['pokemon_data'].get('num_upgrades', 0),
                'move_1': member['pokemon_data'].get('move_1'),
                'move_2': member['pokemon_data'].get('move_2'),
                'height': member['pokemon_data'].get('height_m'),
                'weight': member['pokemon_data'].get('weight_kg'),
                'stamina': member['pokemon_data'].get('stamina'),
                'stamina_max': member['pokemon_data'].get('stamina_max'),
                'cp_multiplier': member['pokemon_data'].get('cp_multiplier'),
                'additional_cp_multiplier': member['pokemon_data'].get('additional_cp_multiplier', 0),
                'iv_defense': member['pokemon_data'].get('individual_defense', 0),
                'iv_stamina': member['pokemon_data'].get('individual_stamina', 0),
                'iv_attack': member['pokemon_data'].get('individual_attack', 0),
                'last_seen': datetime.utcnow(),
            }

            trainers[i] = {
                'name': member['trainer_public_profile']['name'],
                'team': gym_state['fort_data']['owned_by_team'],
                'level': member['trainer_public_profile']['level'],
                'last_seen': datetime.utcnow(),
            }

            if args.webhooks:
                webhook_data['pokemon'].append({
                    'pokemon_uid': member['pokemon_data']['id'],
                    'pokemon_id': member['pokemon_data']['pokemon_id'],
                    'cp': member['pokemon_data']['cp'],
                    'num_upgrades': member['pokemon_data'].get('num_upgrades', 0),
                    'move_1': member['pokemon_data'].get('move_1'),
                    'move_2': member['pokemon_data'].get('move_2'),
                    'height': member['pokemon_data'].get('height_m'),
                    'weight': member['pokemon_data'].get('weight_kg'),
                    'stamina': member['pokemon_data'].get('stamina'),
                    'stamina_max': member['pokemon_data'].get('stamina_max'),
                    'cp_multiplier': member['pokemon_data'].get('cp_multiplier'),
                    'additional_cp_multiplier': member['pokemon_data'].get('additional_cp_multiplier', 0),
                    'iv_defense': member['pokemon_data'].get('individual_defense', 0),
                    'iv_stamina': member['pokemon_data'].get('individual_stamina', 0),
                    'iv_attack': member['pokemon_data'].get('individual_attack', 0),
                    'trainer_name': member['trainer_public_profile']['name'],
                    'trainer_level': member['trainer_public_profile']['level'],
                })

            i += 1
        if args.webhooks:
            wh_update_queue.put(('gym_details', webhook_data))

    # All this database stuff is synchronous (not using the upsert queue) on purpose.
    # Since the search workers load the GymDetails model from the database to determine if a gym
    # needs rescanned, we need to be sure the GymDetails get fully committed to the database before moving on.
    #
    # We _could_ synchronously upsert GymDetails, then queue the other tables for
    # upsert, but that would put that Gym's overall information in a weird non-atomic state.

    # Upsert all the models.
    if len(gym_details):
        bulk_upsert(GymDetails, gym_details)
    if len(gym_pokemon):
        bulk_upsert(GymPokemon, gym_pokemon)
    if len(trainers):
        bulk_upsert(Trainer, trainers)

    # This needs to be completed in a transaction, because we don't want any other thread or process
    # to mess with the GymMembers for the gyms we're updating while we're updating the bridge table.
    with flaskDb.database.transaction():
        # Get rid of all the gym members, we're going to insert new records.
        if len(gym_details):
            DeleteQuery(GymMember).where(GymMember.gym_id << list(gym_details.keys())).execute()

        # Insert new gym members.
        if len(gym_members):
            bulk_upsert(GymMember, gym_members)

    log.info('Upserted %d gyms and %d gym members',
             len(gym_details),
             len(gym_members))


def db_updater(args, q):
    # The forever loop.
    while True:
        try:

            while True:
                try:
                    flaskDb.connect_db()
                    break
                except Exception as e:
                    log.warning('%s... Retrying', e)

            # Loop the queue.
            while True:
                model, data = q.get()
                bulk_upsert(model, data)
                q.task_done()
                log.debug('Upserted to %s, %d records (upsert queue remaining: %d)',
                          model.__name__,
                          len(data),
                          q.qsize())
                if q.qsize() > 50:
                    log.warning("DB queue is > 50 (@%d); try increasing --db-threads", q.qsize())
            del model
            del data

        except Exception as e:
            log.exception('Exception in db_updater: %s', e)


def clean_db_loop(args):
    while True:
        try:
            # Clean out old scanned locations.
            query = (ScannedLocation
                     .delete()
                     .where((ScannedLocation.last_modified <
                             (datetime.utcnow() - timedelta(minutes=30)))))
            query.execute()

            query = (MainWorker
                     .delete()
                     .where((ScannedLocation.last_modified <
                             (datetime.utcnow() - timedelta(minutes=30)))))
            query.execute()

            if args.account_rest_interval:
                query = (WorkerStatus
                         .update(flag=0)
                         .where((WorkerStatus.flag > 1) &
                                (WorkerStatus.flag < 5) &
                                (WorkerStatus.last_modified < (datetime.utcnow() - timedelta(seconds=args.account_rest_interval)))))
                query.execute()  # Release all flagged accounts that arent banned or in use

            query = (WorkerStatus
                     .update(flag=0, worker_name='')
                     .where((WorkerStatus.last_modified < (datetime.utcnow() - timedelta(minutes=5))) &
                            (WorkerStatus.flag == 1)))
            query.execute()

            # Disable expired HashKeys
            query = (HashKeys
                     .delete()
                     .where(HashKeys.expires < (datetime.utcnow() - timedelta(days=1))))
            query.execute()

            # Reset key counters
            query = (HashKeys
                 .update(peak=0, remaining=HashKeys.maximum, last_updated=datetime.utcnow())
                 .where(HashKeys.key != 'Totals'))
            query.execute()

            # Remove active modifier from expired lured pokestops.
            query = (Pokestop
                     .update(lure_expiration=None, active_fort_modifier=None)
                     .where(Pokestop.lure_expiration < datetime.utcnow()))
            query.execute()

            # If desired, clear old pokemon spawns.
            if args.purge_data > 0:
                query = (Pokemon
                         .delete()
                         .where((Pokemon.disappear_time <
                                (datetime.utcnow() - timedelta(hours=args.purge_data)))))
                query.execute()

            log.info('Regular database cleaning complete')
            time.sleep(60)
        except Exception as e:
            log.exception('Exception in clean_db_loop: %s', e)


def bulk_upsert(cls, data):
    num_rows = len(list(data.values()))
    i = 0

    if args.db_type == 'mysql':
        step = 120
    else:
        # SQLite has a default max number of parameters of 999,
        # so we need to limit how many rows we insert for it.
        step = 50

    while i < num_rows:
        log.debug('Inserting items %d to %d', i, min(i + step, num_rows))
        try:
            InsertQuery(cls, rows=list(data.values())[i:min(i + step, num_rows)]).upsert().execute()
        except Exception as e:
            log.warning('%s... Retrying', e)
            time.sleep(2)
            continue

        i += step


def create_tables(db):
    db.connect()
    verify_database_schema(db)
    db.create_tables([Pokemon, Pokestop, Gym, ScannedLocation, GymDetails, GymMember, GymPokemon, Trainer, MainWorker, WorkerStatus, Spawnpoints, HashKeys, UserData], safe=True)
    db.close()


def drop_tables(db):
    db.connect()
    db.drop_tables([Pokemon, ScannedLocation, GymDetails, GymMember, GymPokemon, Trainer, MainWorker, Spawnpoints, Versions, HashKeys], safe=True)
    db.close()


def verify_database_schema(db):
    if not Versions.table_exists():
        db.create_tables([Versions])

        if ScannedLocation.table_exists():
            # Versions table didn't exist, but there were tables. This must mean the user
            # is coming from a database that existed before we started tracking the schema
            # version. Perform a full upgrade.
            InsertQuery(Versions, {Versions.key: 'schema_version', Versions.val: 0}).execute()
            database_migrate(db, 0)
        else:
            InsertQuery(Versions, {Versions.key: 'schema_version', Versions.val: db_schema_version}).execute()

    else:
        db_ver = Versions.get(Versions.key == 'schema_version').val

        if db_ver < db_schema_version:
            database_migrate(db, db_ver)

        elif db_ver > db_schema_version:
            log.error("Your database version (%i) appears to be newer than the code supports (%i).",
                      db_ver, db_schema_version)
            log.error("Please upgrade your code base or drop all tables in your database.")
            sys.exit(1)

        if not args.only_server:
            if len(args.accounts) > 0:
                WorkerStatus.populate_db(args.accounts)
            
            if len(args.hash_key) > 0:
                HashKeys.populate_db(args.hash_key)


def database_migrate(db, old_ver):
    # Update database schema version.
    Versions.update(val=db_schema_version).where(Versions.key == 'schema_version').execute()

    log.info("Detected database version %i, updating to %i", old_ver, db_schema_version)

    # Perform migrations here.
    migrator = None
    if args.db_type == 'mysql':
        migrator = MySQLMigrator(db)
    else:
        migrator = SqliteMigrator(db)

#   No longer necessary, we're doing this at schema 4 as well.
#    if old_ver < 1:
#        db.drop_tables([ScannedLocation])

    if old_ver < 2:
        migrate(migrator.add_column('pokestop', 'encounter_id', CharField(max_length=50, null=True)))

    if old_ver < 3:
        migrate(
            migrator.add_column('pokestop', 'active_fort_modifier', CharField(max_length=50, null=True)),
            migrator.drop_column('pokestop', 'encounter_id'),
            migrator.drop_column('pokestop', 'active_pokemon_id')
        )

    if old_ver < 4:
        db.drop_tables([ScannedLocation])

    if old_ver < 5:
        # Some pokemon were added before the 595 bug was "fixed".
        # Clean those up for a better UX.
        query = (Pokemon
                 .delete()
                 .where(Pokemon.disappear_time >
                        (datetime.utcnow() - timedelta(hours=24))))
        query.execute()

    if old_ver < 6:
        migrate(
            migrator.add_column('gym', 'last_scanned', DateTimeField(null=True)),
        )

    if old_ver < 7:
        migrate(
            migrator.drop_column('gymdetails', 'description'),
            migrator.add_column('gymdetails', 'description', TextField(null=True, default=""))
        )

    if old_ver < 8:
        migrate(
            migrator.add_column('pokemon', 'individual_attack', IntegerField(null=True, default=0)),
            migrator.add_column('pokemon', 'individual_defense', IntegerField(null=True, default=0)),
            migrator.add_column('pokemon', 'individual_stamina', IntegerField(null=True, default=0)),
            migrator.add_column('pokemon', 'move_1', IntegerField(null=True, default=0)),
            migrator.add_column('pokemon', 'move_2', IntegerField(null=True, default=0))
        )

    if old_ver < 9:
        migrate(
            migrator.add_column('pokemon', 'last_modified', DateTimeField(null=True, index=True)),
            migrator.add_column('pokestop', 'last_updated', DateTimeField(null=True, index=True))
        )

    if old_ver < 10:
        migrate(
            migrator.add_column('workerstatus', 'pword', CharField(null=True)),
            migrator.add_column('workerstatus', 'captcha', IntegerField(default=0)),
            migrator.add_column('workerstatus', 'lat', DoubleField(default=50)),
            migrator.add_column('workerstatus', 'lon', DoubleField(default=-105)),
            migrator.add_column('workerstatus', 'last_scan', IntegerField(default=0)),
            migrator.add_column('workerstatus', 'flag', IntegerField(default=0))
        )

def numberToBase(n, b):
    if n == 0:
        return [0]
    digits = []
    while n:
        digits.append(int(n % b))
        n /= b
    return digits[::-1]

def checkspawns(mainlist, removelist):
    remaining = []
    for i in mainlist:
        if i['spawnpoint_id'] not in removelist:
            remaining.append(i)

    return remaining

def get_circle(radius, steps):
    overlap = 0.8660257142857143 * radius
    step_distance = ((steps - 1) * overlap) + radius

    return step_distance
