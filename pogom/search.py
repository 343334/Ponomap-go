 #!/usr/bin/python
# -*- coding: utf-8 -*-

'''
Search Architecture:
 - Have a list of accounts
 - Create an "overseer" thread
 - Search Overseer:
   - Tracks incoming new location values
   - Tracks "paused state"
   - During pause or new location will clears current search queue
   - Starts search_worker threads
 - Search Worker Threads each:
   - Have a unique API login
   - Listens to the same Queue for areas to scan
   - Can re-login as needed
   - Pushes finds to db queue and webhook queue
'''
from __future__ import division
from __future__ import print_function
from __future__ import absolute_import

from builtins import input
from builtins import str
from builtins import range
from past.utils import old_div
import logging
import math
import os
import random
import time
import geopy
import geopy.distance
import requests

from datetime import datetime, timedelta
from dateutils import timezone
from threading import Thread, Lock
from queue import Queue, Empty

from pgoapi import PGoApi
from pgoapi.utilities import f2i
from pgoapi import utilities as util
from pgoapi.exceptions import AuthException
from pgoapi.hash_server import HashServer
from geopy.distance import vincenty

from . import config
from .models import parse_map, GymDetails, parse_gyms, MainWorker, WorkerStatus, Spawnpoints, HashKeys, Gym, Pokestop
from .fakePogoApi import FakePogoApi
from .utils import now, cur_sec, get_args, equi_rect_distance, clear_dict_response
from .transform import get_new_coords
from . import schedulers

from . import terminalsize

log = logging.getLogger(__name__)

TIMESTAMP = '\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000'

loginDelayLock = Lock()


# Apply a location jitter.
def jitterLocation(location=None, maxMeters=10):
    origin = geopy.Point(location[0], location[1])
    b = random.randint(0, 360)
    d = math.sqrt(random.random()) * (old_div(float(maxMeters), 1000))
    destination = geopy.distance.distance(kilometers=d).destination(origin, b)
    return (destination.latitude, destination.longitude, location[2])


# Thread to handle user input.
def switch_status_printer(display_type, current_page, mainlog, loglevel):
    # Get a reference to the root logger.
    mainlog = logging.getLogger()
    # Disable logging of the first handler - the stream handler, and disable it's output.
    mainlog.handlers[0].setLevel(logging.CRITICAL)

    while True:
        # Wait for the user to press a key.
        command = input()

        if command == '':
            # Switch between logging and display.
            if display_type[0] != 'logs':
                # Disable display, enable on screen logging.
                mainlog.handlers[0].setLevel(loglevel)
                display_type[0] = 'logs'
                # If logs are going slowly, sometimes it's hard to tell you switched.  Make it clear.
                print('Showing logs...')
            elif display_type[0] == 'logs':
                # Enable display, disable on screen logging (except for critical messages).
                mainlog.handlers[0].setLevel(logging.CRITICAL)
                display_type[0] = 'workers'
        elif command.isdigit():
                current_page[0] = int(command)
                mainlog.handlers[0].setLevel(logging.CRITICAL)
                display_type[0] = 'workers'
        elif command.lower() == 'f':
                mainlog.handlers[0].setLevel(logging.CRITICAL)
                display_type[0] = 'failedaccounts'


# Thread to print out the status of each worker.
def status_printer(threadStatus, search_items_queue_array, db_updates_queue, wh_queue, account_failures, hash_key, key_scheduler):
    display_type = ["workers"]
    current_page = [1]
    mainlog = logging.getLogger()
    loglevel = mainlog.getEffectiveLevel()
    args = get_args()

    # Start another thread to get user input.
    t = Thread(target=switch_status_printer,
               name='switch_status_printer',
               args=(display_type, current_page, mainlog, loglevel))
    t.daemon = True
    t.start()

    while True:
        time.sleep(1)

        if display_type[0] == 'logs':
            # In log display mode, we don't want to show anything.
            continue

        # Create a list to hold all the status lines, so they can be printed all at once to reduce flicker.
        status_text = []

        if display_type[0] == 'workers':

            # Get the terminal size.
            width, height = terminalsize.get_terminal_size()
            # Queue and overseer take 2 lines.  Switch message takes up 2 lines.  Remove an extra 2 for things like screen status lines.
            usable_height = height - 6
            # Prevent people running terminals only 6 lines high from getting a divide by zero.
            if usable_height < 1:
                usable_height = 1

            # Calculate total skipped items.
            skip_total = 0
            captchacount = 0
            usercount = 0
            successcount = 0
            failcount = 0
            emptycount = 0
            solved = 0
            retrycount = 0
            hashcount = 0
            elapsed = 1
            for item in threadStatus:
                elapsed = now() - threadStatus['Overseer']['time']
                if elapsed == 0:
                        elapsed = 1
                if 'skip' in threadStatus[item]:
                    skip_total += threadStatus[item]['skip']
                if 'captcha' in threadStatus[item]:
                    captchacount += threadStatus[item]['captcha']
                if 'noitems' in threadStatus[item]:
                    emptycount += threadStatus[item]['noitems']
                if 'fail' in threadStatus[item]:
                    failcount += threadStatus[item]['fail']
                if 'success' in threadStatus[item]:
                    successcount += threadStatus[item]['success']
                if 'retries' in threadStatus[item]:
                    retrycount += threadStatus[item]['retries']
                if 'csolved' in threadStatus[item]:
                    solved += threadStatus[item]['csolved']
                if 'hashuse' in threadStatus[item]:
                    hashcount += threadStatus[item]['hashuse']

            # Print the queue length.
            search_items_queue_size = 0
            for i in range(0, len(search_items_queue_array)):
                search_items_queue_size += search_items_queue_array[i].qsize()

            status_text.append('Area: {}, Queues: {} scans, {} DB, {} webhook.  Skipped items: {}. Spare accounts: {} | On hold: {} | In use: {}'
                               .format(args.status_name, search_items_queue_size, db_updates_queue.qsize(), wh_queue.qsize(), skip_total, WorkerStatus.get_unused_accounts(), WorkerStatus.get_held_accounts(), WorkerStatus.get_active(args.status_name)))

            # Print status of overseer.
            status_text.append('Started: {} | {} Overseer: {}'.format(time.strftime("%H:%M:%S", time.gmtime(threadStatus['Overseer']['time'])), threadStatus['Overseer']['scheduler'], threadStatus['Overseer']['message']))

            # Calculate the total number of pages.  Subtracting 1 for the overseer.
            total_pages = math.ceil(old_div((len(threadStatus) - 1), float(usable_height)))

            # Prevent moving outside the valid range of pages.
            if current_page[0] > total_pages:
                current_page[0] = total_pages
            if current_page[0] < 1:
                current_page[0] = 1

            # Calculate which lines to print.
            start_line = usable_height * (current_page[0] - 1)
            end_line = start_line + usable_height
            current_line = 1

            # Find the longest username and proxy.
            userlen = 4
            proxylen = 5
            for item in threadStatus:
                if threadStatus[item]['type'] == 'Worker':
                    userlen = max(userlen, len(threadStatus[item]['user']))
                    if 'proxy_display' in threadStatus[item]:
                        proxylen = max(proxylen, len(str(threadStatus[item]['proxy_display'])))

            # How pretty.
            status = '{:12} | {:7} | {:' + str(userlen) + '} | {:' + str(proxylen) + '} | {:7} | {:6} | {:5} | {:7} | {:8} | {:7} | {:6} | {:10}'

            # Print the worker status.
            status_text.append(status.format('Worker ID', 'Runtime', 'User', 'Proxy', 'Success', 'Failed', 'Empty', 'Skipped', 'Captchas', 'Retries', 'Hashes', 'Message'))
            for item in sorted(threadStatus):
                if(threadStatus[item]['type'] == 'Worker'):
                    if 'starttime' in threadStatus[item]:
                        started = threadStatus[item]['starttime']
                    else:
                        started = now()
                    current_line += 1

                    # Skip over items that don't belong on this page.
                    if current_line < start_line:
                        continue
                    if current_line > end_line:
                        break

                    status_text.append(status.format(item, abs(now() - started), threadStatus[item]['user'], threadStatus[item]['proxy_display'], threadStatus[item]['success'], threadStatus[item]['fail'], threadStatus[item]['noitems'], threadStatus[item]['skip'], threadStatus[item]['captcha'], threadStatus[item]['retries'], threadStatus[item]['hashuse'], threadStatus[item]['message']))

        elif display_type[0] == 'failedaccounts':
            status_text.append('-----------------------------------------')
            status_text.append('Accounts on hold:')
            status_text.append('-----------------------------------------')

            # Find the longest account name.
            userlen = 4
            for account in account_failures:
                userlen = max(userlen, len(account['account']['username']))

            status = '{:' + str(userlen) + '} | {:10} | {:20}'
            status_text.append(status.format('User', 'Hold Time', 'Reason'))

            for account in account_failures:
                status_text.append(status.format(account['account']['username'], time.strftime('%H:%M:%S', time.localtime(account['last_fail_time'])), account['reason']))

        # Print the status_text for the current screen.
        status_text.append('Total active: {}  |  Success: {} ({}/hr) | Fails: {} | Empties: {} ({}/hr) | Skips: {} | Retries: {} | Hashes: {} ({}/min) | Captchas: {} ({}/hr)|${:2}/hr|${:2}/d|${:2} spent'.format(WorkerStatus.get_active(), successcount, (successcount * 3600 / elapsed), failcount, emptycount, (emptycount * 3600 / elapsed), skip_total, retrycount, hashcount, (hashcount * 60 / elapsed), captchacount, (captchacount * 3600 / elapsed), (captchacount * 3600 / elapsed) * 0.003, ((captchacount * 3600 / elapsed) * 0.003 * 24), (solved * 0.003)))
        status_text.append('Page {}/{}. Page number to switch pages. F to show on hold accounts. <ENTER> alone to switch between status and log view'.format(current_page[0], total_pages))
        # Clear the screen.
        os.system('cls' if os.name == 'nt' else 'clear')
        # Print status.
        print("\n".join(status_text))


# The account recycler monitors failed accounts and places them back in the account queue 2 hours after they failed.
# This allows accounts that were soft banned to be retried after giving them a chance to cool down.
def account_recycler(account_failures, args):
    while True:
        # Run once a minute.
        time.sleep(60)
        log.info('Account recycler running. Checking status of {} accounts'.format(len(account_failures)))

        # Create a new copy of the failure list to search through, so we can iterate through it without it changing.
        failed_temp = list(account_failures)

        # Search through the list for any item that last failed before 2 hours ago.
        ok_time = now() - args.account_rest_interval
        for a in failed_temp:
            if a['last_fail_time'] <= ok_time:
                # Remove the account from the real list, and add to the account queue.
                log.info('Account {} returning to active duty.'.format(a['account']['username']))
                account_failures.remove(a)
                query = (WorkerStatus
                         .update(flag=0, worker_name='')
                         .where(WorkerStatus.username == a['account']['username']) &
                               (WorkerStatus.flag < 5))
                query.execute()  # do not release flag 5 (banned) accounts.
            else:
                if 'notified' not in a:
                    log.info('Account {} needs to cool off for {} minutes due to {}'.format(a['account']['username'], round(old_div((a['last_fail_time'] - ok_time), 60), 0), a['reason']))
                    a['notified'] = True


def worker_status_db_thread(threads_status, name, db_updates_queue):
    #log.info("Clearing previous statuses for '%s' worker", name)
    #WorkerStatus.delete().where(WorkerStatus.worker_name == name).execute()

    while True:
        workers = {}
        overseer = None
        for status in list(threads_status.values()):
            if status['type'] == 'Overseer':
                overseer = {
                    'worker_name': name,
                    'message': status['message'],
                    'method': status['scheduler'],
                    'last_modified': datetime.utcnow()
                }
        if overseer is not None:
            db_updates_queue.put((MainWorker, {0: overseer}))
            #db_updates_queue.put((WorkerStatus, workers))
        time.sleep(3)


# The main search loop that keeps an eye on the over all process.
def search_overseer_thread(args, new_location_queue, pause_bit, heartb, db_updates_queue, wh_queue):

    log.info('Search overseer starting')

    search_items_queue_array = []
    scheduler_array = []
    threadStatus = {}
    key_scheduler = None

    '''
    Create a queue of accounts for workers to pull from. When a worker has failed too many times,
    it can get a new account from the queue and reinitialize the API. Workers should return accounts
    to the queue so they can be tried again later, but must wait a bit before doing do so to
    prevent accounts from being cycled through too quickly.
    '''

    #for account in args.accounts:
    #    account_queue.put(account)

    # Create a list for failed accounts.
    account_failures = []

    threadStatus['Overseer'] = {
        'message': 'Initializing',
        'type': 'Overseer',
        'time': now(),
        'scheduler': args.scheduler
    }

    # Create the key Scheduler
    if args.hash_key:
        log.info('Enabling hashing key scheduler...')
        key_scheduler = schedulers.KeyScheduler(args.hash_key, db_updates_queue)

    # Create account recycler thread.
    #log.info('Starting account recycler thread')
    #t = Thread(target=account_recycler, name='account-recycler', args=(account_failures, args))
    #t.daemon = True
    #t.start()

    if args.status_name is not None:
        log.info('Starting status database thread')
        t = Thread(target=worker_status_db_thread,
                   name='status_worker_db',
                   args=(threadStatus, args.status_name, db_updates_queue))
        t.daemon = True
        t.start()

    #search_items_queue = Queue()
    # Create the appropriate type of scheduler to handle the search queue.
    #scheduler = schedulers.SchedulerFactory.get_scheduler(args.scheduler, [search_items_queue], threadStatus, args)

    #scheduler_array.append(scheduler)
    #search_items_queue_array.append(search_items_queue)

    # A place to track the current location.
    current_location = False
    workersstarted = False

    # The real work starts here but will halt on pause_bit.set().
    while True:

        if args.on_demand_timeout > 0 and (now() - args.on_demand_timeout) > heartb[0]:
            pause_bit.set()
            log.info("Searching paused due to inactivity...")

        # Wait here while scanning is paused.
        while pause_bit.is_set():
            for i in range(0, len(scheduler_array)):
                scheduler_array[i].scanning_paused()
            time.sleep(1)

        # If a new location has been passed to us, get the most recent one.
        if not new_location_queue.empty():
            log.info('New location caught, moving search grid')
            try:
                while True:
                    current_location = new_location_queue.get_nowait()
            except Empty:
                pass

            step_distance = 0.07

            if args.no_pokemon:
                step_distance = 0.45

            if hasattr(args, 'workers') and args.workers > 0:
                thrds = args.workers
            else:
                thrds = 0

            locations = generate_hive_locations(args, current_location, step_distance, args.step_limit, thrds)

            if not workersstarted:
                x = 1
                y = 0
                i = 0
                while i in range(0, len(locations)):  # we can't do "sum(locations[i][3]) / args.spawns_per_worker" because an individual hex could easily have more spawns.
                    spawns = locations[i][3]
                    log.debug('Threads starting, {} spawnpoints in this workers hex'.format(spawns))

                    if x == 1:  # skipping this if statement creates workers in the same hex/queue. First worker in hex always needs a new queue.
                        log.debug('New location')
                        log.debug("Got enough workers for the spawnpoint count, or not spawnpoint scanning.")
                        log.debug ('i: {} | args.beehive: {} | workers per hive: {} | spawns: {} | x: {} | spawns/x: {} | spawns per worker: {}'.format(i, args.beehive, args.workers_per_hive, spawns, x, (old_div(spawns, x)), args.spawns_per_worker))
                        search_items_queue = Queue()
                        # Create the appropriate type of scheduler to handle the search queue.
                        scheduler = schedulers.SchedulerFactory.get_scheduler(args.scheduler, [search_items_queue], threadStatus, args)

                        scheduler_array.append(scheduler)
                        search_items_queue_array.append(search_items_queue)
                        

                    # Set proxy for each worker, using round robin.
                    proxy_display = 'No'
                    proxy_url = False

                    if args.proxy:
                        proxy_display = proxy_url = args.proxy[y % len(args.proxy)]
                        if args.proxy_display.upper() != 'FULL':
                            proxy_display = y % len(args.proxy)

                    workerId = 'Worker {:03}'.format(y)
                    threadStatus[workerId] = {
                        'type': 'Worker',
                        'message': 'Creating thread...',
                        'success': 0,
                        'fail': 0,
                        'noitems': 0,
                        'skip': 0,
                        'captcha': 0,
                        'csolved': 0,
                        'retries': 0,
                        'hashuse': 0,
                        'user': '',
                        'proxy_display': proxy_display,
                        'proxy_url': proxy_url,
                        'location': False,
                        'last_scan_time': 0,
                    }

                    t = Thread(target=search_worker_thread,
                               name='search-worker-{}'.format(y),
                                args=(args, account_failures, search_items_queue, pause_bit,
                                     threadStatus[workerId],
                                     db_updates_queue, wh_queue, key_scheduler, y))
                    t.daemon = True
                    t.start()

                    y += 1  # y is our thread counter used for starting overall workers above
                    if (args.spawnpoint_scanning and (old_div(spawns, x)) > args.spawns_per_worker) or (args.beehive and x < args.workers_per_hive):
                        log.debug('still not enough workers, starting another thread')
                        x += 1
                    else:
                        i += 1  # advance the location when we're satisfied with the number of workers.
                        x = 1  # reset our worker-in-hex counter

                if(args.print_status):
                    log.info('Starting status printer thread')
                    t = Thread(target=status_printer,
                               name='status_printer',
                               args=(threadStatus, search_items_queue_array, db_updates_queue, wh_queue, account_failures, args.hash_key, key_scheduler))
                    t.daemon = True
                    t.start()

            workersstarted = True
            x = 0
            for i in range(0, len(scheduler_array)):
                log.debug('Scheduler array size: {}, locations: {}, x: {}, i: {}'.format(len(scheduler_array), len(locations), x, i))
                if x >= len(locations):
                    x = 0
                scheduler_array[i].location_changed(locations[x])  # above code should have created the same number of arrays as locations
                log.debug('Schedulers: {} | Locations: {}'.format(len(scheduler_array), len(locations)))  # let's check.
                x += 1
            del locations

        # If there are no search_items_queue either the loop has finished (or been
        # cleared above) -- either way, time to fill it back up
        for i in range(0, len(search_items_queue_array)):
            if search_items_queue_array[i].empty():
                log.debug('Search queue empty, scheduling more items to scan')
                scheduler_array[i].schedule()
            else:
                nextitem = search_items_queue_array[i].queue[0]
                threadStatus['Overseer']['message'] = 'Processing search queue, next item is {:6f},{:6f}'.format(nextitem[1][0], nextitem[1][1])
                # If times are specified, print the time of the next queue item, and how many seconds ahead/behind realtime.
                if nextitem[2]:
                    threadStatus['Overseer']['message'] += ' @ {}'.format(time.strftime('%H:%M:%S', time.localtime(nextitem[2])))
                    if nextitem[2] > now():
                        threadStatus['Overseer']['message'] += ' ({}s ahead)'.format(nextitem[2] - now())
                    else:
                        threadStatus['Overseer']['message'] += ' ({}s behind)'.format(now() - nextitem[2])



        # Now we just give a little pause here.
        time.sleep(1)

# Generates the list of locations to scan
def generate_hive_locations(args, current_location, step_distance, step_limit, thrds):
    NORTH = 0
    EAST = 90
    SOUTH = 180
    WEST = 270

    xdist = math.sqrt(3) * step_distance  # dist between column centers
    ydist = 3 * (old_div(step_distance, 2))  # dist between row centers

    results = []
    delta = [1, 1, 1, 1]

    results = ringappend(args, current_location, results, step_limit)
    hexes, ring, count, limit = delta

    loc = current_location

    if args.by_hex_count > 1:  # how many hexes regardless of empty or not
        limit = args.by_hex_count
        delta = [1, 0, 0]
    elif args.leaps > 1:  # how many complete rings
        limit = args.leaps
        delta = [0, 1, 0]
    elif args.by_valid_count > 1:  # how many hexes with scannable items
        limit = args.by_count
        delta = [0, 0, 1]
    else:
        limit = 1
        delta = [1, 0, 0]


    while (hexes * delta[0]) + (ring * delta[1]) + (len(results) * delta[2]) < limit:
        loc = get_new_coords(loc, ydist * (step_limit - 1), NORTH)
        loc = get_new_coords(loc, xdist * (1.5 * step_limit - 0.5), EAST)
        hexes += 1
        results = ringappend(args, loc, results, step_limit)

        for i in range(ring):
            loc = get_new_coords(loc, ydist * step_limit, NORTH)
            loc = get_new_coords(loc, xdist * (1.5 * step_limit - 1), WEST)
            hexes += 1
            results = ringappend(args, loc, results, step_limit)

        for i in range(ring):
            loc = get_new_coords(loc, ydist * (step_limit - 1), SOUTH)
            loc = get_new_coords(loc, xdist * (1.5 * step_limit - 0.5), WEST)
            hexes += 1
            results = ringappend(args, loc, results, step_limit)

        for i in range(ring):
            loc = get_new_coords(loc, ydist * (2 * step_limit - 1), SOUTH)
            loc = get_new_coords(loc, xdist * 0.5, WEST)
            hexes += 1
            results = ringappend(args, loc, results, step_limit)

        for i in range(ring):
            loc = get_new_coords(loc, ydist * (step_limit), SOUTH)
            loc = get_new_coords(loc, xdist * (1.5 * step_limit - 1), EAST)
            hexes += 1
            results = ringappend(args, loc, results, step_limit)

        for i in range(ring):
            loc = get_new_coords(loc, ydist * (step_limit - 1), NORTH)
            loc = get_new_coords(loc, xdist * (1.5 * step_limit - 0.5), EAST)
            hexes += 1
            results = ringappend(args, loc, results, step_limit)
        # Back to start
        for i in range(ring - 1):
            loc = get_new_coords(loc, ydist * (2 * step_limit - 1), NORTH)
            loc = get_new_coords(loc, xdist * 0.5, EAST)
            hexes += 1
            results = ringappend(args, loc, results, step_limit)

        loc = get_new_coords(loc, ydist * (2 * step_limit - 1), NORTH)
        loc = get_new_coords(loc, xdist * 0.5, EAST)

        ring += 1

    log.info('Hexes calculated: {} | Rings/Leaps: {} | Populated hexes: {}'.format(hexes, ring, len(results)))
    time.sleep(2)
    return results

def ringappend(args, loc, results, steps):
    


def search_worker_thread(args, account_failures, search_items_queue, pause_bit, status, dbq, whq, key_scheduler, wid):
    step_location = []
    log.debug('Search worker thread starting')
    status['csolved'] = 0
    slimit = args.speed_limit
    firstrun = True

    # The outer forever loop restarts only when the inner one is intentionally exited - which should only be done when the worker is failing too often, and probably banned.
    # This reinitializes the API and grabs a new account from the queue.
    while True:
        try:
            # Get an account.
            #account = account_queue.get()
            while search_items_queue.qsize() == 0:
                status['message'] = 'Waiting to get work queue...'
                time.sleep(5)  # stop this worker from ever running or grabbing a worker while the queue is empty. If it never fills, a worker is never assigned
            if firstrun:
                step, next_location, appears, leaves = search_items_queue.get()
                status['lat'], status['lon'], status['alt'] = next_location
                # Delay each thread start time so that logins occur after delay.
                loginDelayLock.acquire()
                delay = (args.login_delay) + (old_div((random.random() - .5), 2))
                status['message'] = 'Delaying thread startup for ' + str(delay) + ' seconds'
                time.sleep(delay)
                loginDelayLock.release()
            status['message'] = 'Getting closest worker'
            account = WorkerStatus.get_closest_available(next_location[0], next_location[1], wid)
            status['starttime'] = now()
            if not account['lat']:
                account['lat'], account['lon'] = next_location
            step_location = account['lat'], account['lon']
            status['message'] = 'Switching to account {}'.format(account['username'])
            log.debug('current time: {}'.format(now()))
            status['user'] = account['username']
            status['pass'] = account['pass']
            log.info(status['message'])

            # New lease of life right here.
            status['fail'] = 0
            status['success'] = 0
            status['noitems'] = 0
            status['skip'] = 0
            status['captcha'] = 0
            status['location'] = False
            if not account['last_scan']:
                account['last_scan'] = now()
            status['last_scan_time'] = account['last_scan']
            status['hashuse'] = 0
            status['retries'] = 0

            # Only sleep when consecutive_fails reaches max_failures, overall fails for stat purposes.
            consecutive_fails = 0
            consecutive_empties = 0
            consecutive_blind = 0

            # Create the API instance this will use.
            if args.mock != '':
                api = FakePogoApi(args.mock)
            else:
                api = PGoApi()

            if status['proxy_url']:
                log.debug("Using proxy %s", status['proxy_url'])
                api.set_proxy({'http': status['proxy_url'], 'https': status['proxy_url']})

            # The forever loop for the searches.
            log.debug('starting search loop')
            
            while True:
                # If this account has been messing up too hard, let it rest.
                if (consecutive_fails + consecutive_empties + consecutive_blind) >= args.max_failures:  # if the worker shits the bed, get rid of it.
                    status['message'] = 'Account {} failed more than {} scans; possibly bad account. Switching accounts...'.format(account['username'], args.max_failures)
                    log.warning(status['message'])
                    account_failures.append({'account': account, 'last_fail_time': now(), 'reason': 'failures'})
                    query = (WorkerStatus
                             .update(flag=2, last_modified=datetime.utcnow(), worker_name='')
                             .where(WorkerStatus.username == account['username']))
                    query.execute()
                    break  # Exit this loop to get a new account and have the API recreated.
                
                while pause_bit.is_set():
                    status['message'] = 'Scanning paused'
                    time.sleep(2)

                # If this account has been running too long, let it rest.
                if args.account_search_interval is not None:
                    if (status['starttime'] <= (now() - args.account_search_interval)):
                        status['message'] = 'Account {} is being rotated out to rest.'.format(account['username'])
                        log.info(status['message'])
                        account_failures.append({'account': account, 'last_fail_time': now(), 'reason': 'rest interval'})
                        query = (WorkerStatus
                                 .update(flag=3, last_modified=datetime.utcnow(), worker_name='')
                                 .where(WorkerStatus.username == account['username']))
                        query.execute()
                        break

                #if not firstrun:
                step, next_location, appears, leaves = search_items_queue.get()
                status['message'] = 'Got new search item'

                paused = False
                
                randomizer = random.uniform(0.8, 1)
                #log.debug('randomized')
                distance = equi_rect_distance(step_location, next_location)
                elapsed = now() - account['last_scan']
                #log.debug('got distance')
                if distance > 15000:
                    args.speed_limit = 2000 # mach 2 for long distance (15km or more)
                else:
                    args.speed_limit = slimit * randomizer  # return to normal
                status['message'] += ' {} meters away'.format(distance)
                sdelay = max(((old_div(distance, (old_div(args.speed_limit, 3.6)))) - elapsed), args.scan_delay)   # Classic basic physics formula: time = distance divided by velocity (in km/hr), plus a little randomness between 70 and 100% speed.
                #log.debug('{}m for worker to travel at, at a max speed of {} KPH gives us a delay of {}, already waited {}'.format(distance, (args.speed_limit  * randomizer), sdelay, elapsed))
                #if (distance / (elapsed + sdelay)) > (args.speed_limit / 3.6):
                #    status['message'] = 'Worker {} calculated to travel {}m in {} secs for a speed of {} m/s is much too fast!'.format(account['username'], distance, (elapsed + sdelay), (distance / (elapsed + sdelay)))
                #    log.warning(status['message'])
                #    query = (WorkerStatus
                #             .update(flag=0, worker_name='', last_modified=datetime.utcnow())
                #             .where(WorkerStatus.username == account['username']))
                #    query.execute()
                #    break                    

                # Too late?
                if leaves and (now() + sdelay) > (leaves - args.min_seconds_left):
                    # It is slightly silly to put this in status['message'] since it'll be overwritten very shortly after. Oh well.
                    #No sleep here; we've not done anything worth sleeping for. Plus we clearly need to catch up!
                    status['message'] = 'Too late for location {:6f},{:6f}; giving up.'.format(next_location[0], next_location[1])
                    log.info(status['message'])
                    search_items_queue.task_done()
                    status['skip'] += 1
                    continue
                
                # Too soon?
                if appears and (now() + sdelay) < appears:
                    first_loop = True
                    paused = False
                    startwait = now()
                    while now() + sdelay < appears:
                        if pause_bit.is_set():
                            paused = True
                            break  # Why can't python just have `break 2`...
                        remain = appears - now()
                        status['message'] = 'Early for {:6f},{:6f}; waiting {}s...'.format(next_location[0], next_location[1], remain)
                        if first_loop:
                            log.info(status['message'])
                            first_loop = False
                        if startwait - now() > 5:  # prevents releasing workers early while they wait for locations
                            query = (WorkerStatus
                                     .update(last_modified=datetime.utcnow())
                                     .where(WorkerStatus.username == account['username']))
                            query.execute()
                        time.sleep(1)
                    if paused:
                        search_items_queue.task_done()
                        continue
                step_location = next_location
                firstrun = False
                status['message'] += ', sleeping {}s until {}'.format(sdelay, time.strftime('%H:%M:%S', time.localtime(time.time() + sdelay)))
                log.info(status['message'])
                time.sleep(sdelay)

                # Let the api know where we intend to be for this loop.
                # Doing this before check_login so it does not also have to be done there
                # when the auth token is refreshed.
                api.set_position(*step_location)

                if args.hash_key:
                    key = next(key_scheduler)
                    log.debug('Using key {} for this scan.'.format(key))
                    api.activate_hash_server(key)

                # Ok, let's get started -- check our login status.
                check_login(args, account, api, step_location, status['proxy_url'])

                # Putting this message after the check_login so the messages aren't out of order.
                status['message'] = 'Searching at {:6f},{:6f}'.format(step_location[0], step_location[1])
                log.info(status['message'])

                failed = 0
                retries = 0  # reset the retry counter
                while retries <= args.scan_retries:
                    if retries > 0:
                        log.debug('retrying scan {},'.format(retries))
                        status['retries'] += 1
                        if retries == args.scan_retries:
                            log.debug('last attempt')
                        status['message'] += ', sleeping {}s until {}'.format(args.scan_delay, time.strftime('%H:%M:%S', time.localtime(time.time() + args.scan_delay)))
                    elif retries > args.scan_retries:
                        break
                    time.sleep(args.scan_delay * retries)
                    spawns = Spawnpoints.get_spawnpoint_ids(step_location)
                    
                    # Make the actual request. (finally!)
                    response_dict = map_request(args, api, step_location, key_scheduler, args.jitter)
                    status['lastscan'] = now()
                    status['hashuse'] += 1
                    # Only update the database once we've actually made the request.
                    query = (WorkerStatus
                             .update(lat=step_location[0], lon=step_location[1], last_scan=now(), last_modified=datetime.utcnow())
                             .where(WorkerStatus.username == account['username']))
                    query.execute()
                    account['last_scan'] = now()

                    # G'damnit, nothing back. Mark it up, sleep, carry on.
                    if not response_dict:
                        if retries >= args.scan_retries:
                            status['fail'] += 1
                            consecutive_fails += 1
                        status['message'] = 'Invalid response at {:6f},{:6f}, abandoning location'.format(step_location[0], step_location[1])
                        log.error(status['message'])
                        retries += 1
                        continue  # let's try again!
                    #else:
                        #log.debug("server response: {}".format(response_dict))

                    # Got the response, check for captcha, parse it out, then send todo's to db/wh queues.
                    try:
                        # Captcha check
                        if args.captcha_solving:
                            if 'CHECK_CHALLENGE' in response_dict['responses']:
                                captcha_url = response_dict['responses']['CHECK_CHALLENGE']['challenge_url']
                                if len(captcha_url) > 1:
                                    status['captcha'] += 1
                                    status['message'] = 'Account {} is encountering a captcha, starting 2captcha sequence'.format(account['username'])
                                    log.warning(status['message'])
                                    captcha_token = token_request(args, status, captcha_url)
                                    if 'ERROR' in captcha_token:
                                        log.warning("Unable to resolve captcha, please check your 2captcha API key and/or wallet balance")
                                        account_failures.append({'account': account, 'last_fail_time': now(), 'reason': 'captcha failed to verify'})
                                        query = (WorkerStatus
                                                 .update(flag=4, last_modified=datetime.utcnow(), worker_name='')
                                             .where(WorkerStatus.username == account['username']))
                                        query.execute()
                                        failed += 1
                                        log.debug('failure due to 2captcha')
                                        break
                                    else:
                                        status['message'] = 'Retrieved captcha token, attempting to verify challenge for {}'.format(account['username'])
                                        log.info(status['message'])
                                        response = api.verify_challenge(token=captcha_token)
                                        if 'success' in response['responses']['VERIFY_CHALLENGE']:
                                            status['message'] = "Account {} successfully uncaptcha'd".format(account['username'])
                                            status['csolved'] += 1
                                            log.info(status['message'])
                                            # Make another request for the same coordinate since the previous one was captcha'd
                                            response_dict = map_request(args, api, step_location, key_scheduler, args.jitter)
                                        else:
                                            status['message'] = "Account {} failed verifyChallenge, putting away account for now".format(account['username'])
                                            log.info(status['message'])
                                            account_failures.append({'account': account, 'last_fail_time': now(), 'reason': 'catpcha failed to verify'})
                                            query = (WorkerStatus
                                                     .update(flag=5, last_modified=datetime.utcnow(), worker_name='')
                                                     .where(WorkerStatus.username == account['username']))
                                            query.execute()
                                            failed += 1
                                            log.debug('failure due to VERIFY_CHALLENGE')
                                            break
                            else:
                                query = (WorkerStatus
                                         .update(flag=5, last_modified=datetime.utcnow(), worker_name='', message='CHECK_CHALLENGE failed, banned account')
                                         .where(WorkerStatus.username == account['username']))
                                query.execute()
                                failed += 1
                                log.debug('failure due to CHECK_CHALLENGE')
                                break

                        parsed = parse_map(args, response_dict, step_location, dbq, whq, api, spawns, key_scheduler)
                        status['hashuse'] += parsed['hashuses']
                        if parsed['blind'] > 0 and not config['parse_pokemon']:
                            status['message'] = 'No rares detected, possibly blinded account'
                            status['noitems'] += 1
                            consecutive_fails += 1
                        if parsed['count'] > 0:
                            if config['parse_pokemon']:
                                if parsed['pokesfound']:
                                    status['success'] += 1
                                    consecutive_empties = 0
                                    status['message'] = 'Good scan, got pokemon, continuing...'
                                    log.info(status['message'])
                                    search_items_queue.task_done()
                                    break  # Break out of retry loop, we're lookin for pokemon, we got some
                                else:
                                    status['message'] = 'Found stuff to parse, but no pokemon, retrying...'
                                    retries += 1
                                    continue  # We're looking for pokemon, but didn't find any, double check
                            else:
                                status['message'] = 'Found some forts, not looking for Pokemon, continuing'
                                status['success'] += 1
                                log.info(status['message'])
                                consecutive_empties = 0
                                search_items_queue.task_done()
                                break
                                
                        else:  # No pokemon or forts were found, check the nearby list to make sure
                            if parsed['nearby']:  # If we spot a nearby pokemon the scan was good
                                if parsed['pokesfound']:  # Check to see if we actually did find pokemon and it's just not parsing.
                                    status['message'] = 'Pokemon found, but having trouble parsing them!'
                                    log.warning(status['message'])
                                else:
                                    status['message'] = 'Found nearby pokemon, but no pokemon here'
                                    log.info(status['message'])
                                if retries >= args.scan_retries:
                                    status['success'] += 1
                                    consecutive_empties = 0
                                    search_items_queue.task_done()
                                retries += 1
                                continue
                            else:
                                if retries >= args.scan_retries:
                                    status['noitems'] += 1  # set this inside an if statement so we only count up after we give up
                                    consecutive_empties += 1
                                if parsed['nearfort'] > 0:
                                    status['message'] = 'Found a fort, but no pokemon. Either nothing around, or speed limited'
                                else:
                                    status['message'] = 'No nearby pokemon or forts. Either nothing around, or softbanned'
                                log.warning(status['message'])
                                if config['parse_pokemon']:
                                    retries += 1
                                    continue  # Wait, then try scanning again
                                else:
                                    break # Not necessary to retry scan if we aren't even looking for pokemon.

                    except KeyError:
                        failed += 1
                        log.debug('failure due to map exception')
                        status['fail'] += 1
                        consecutive_fails += 1  # wthese aren't in an if statement, because parsing failures need to be handled differently.
                        status['message'] = 'Map parse failed at {:6f},{:6f}, abandoning location. {} may be banned.'.format(step_location[0], step_location[1], account['username'])
                        log.exception(status['message'])

                if response_dict is not None:
                    del response_dict

                if failed > 0:
                    log.debug('failure detected, retrying')
                    continue

                if args.hash_key:
                    key = HashServer.status.get('token')
                    key_instance = key_scheduler.keys[key]
                    key_instance['remaining'] = HashServer.status.get(
                        'remaining', 0)
                    key_instance['maximum'] = (
                        HashServer.status.get('maximum', 0))
                    peak = (
                        key_instance['maximum'] -
                        key_instance['remaining'])

                    if key_instance['peak'] < peak:
                        key_instance['peak'] = peak

                    if key_instance['expires'] is None:
                        expires = HashServer.status.get(
                            'expiration', None)

                        if expires is not None:
                            expires = datetime.utcfromtimestamp(expires)

                        key_instance['expires'] = expires

                    log.debug(
                        ('Hash key {} has {}/{} RPM ' +
                         'left.').format(key, key_instance['remaining'],
                                         key_instance['maximum']))
                    hashkeys = {}
                    hashkeys[key] = key_instance
                    hashkeys[key]['key'] = key
                    dbq.put((HashKeys, hashkeys))

                consecutive_fails = 0
                status['message'] = 'Search at {:6f},{:6f} completed with {} finds; '.format(step_location[0], step_location[1], parsed['count'])
                if parsed['pokesfound']:
                    status['message'] += '; Pokemon were found'
                else:
                    status['message'] += '; No pokemon found'
                log.debug(status['message'])
                

                # Get detailed information about gyms.
                if args.gym_info and parsed:
                    # Build up a list of gyms to update.
                    gyms_to_update = {}
                    log.debug('parsing gym info')
                    for gym in list(parsed['gyms'].values()):
                        # Can only get gym details within 1km of our position.
                        distance = calc_distance(step_location, [gym['latitude'], gym['longitude']])
                        log.debug('checking gym distance')
                        if distance < 0.450:
                            # Check if we already have details on this gym. (if not, get them)
                            try:
                                record = GymDetails.get(gym_id=gym['gym_id'])
                            except GymDetails.DoesNotExist as e:
                                gyms_to_update[gym['gym_id']] = gym
                                log.debug('added gym details')
                                continue

                            # If we have a record of this gym already, check if the gym has been updated since our last update.
                            if record.last_scanned < gym['last_modified']:
                                gyms_to_update[gym['gym_id']] = gym
                                log.debug('updated gym details')
                                continue
                            else:
                                log.debug('Skipping update of gym @ %f/%f, up to date', gym['latitude'], gym['longitude'])
                                continue
                        else:
                            log.debug('Skipping update of gym @ %f/%f, too far away from our location at %f/%f (%fkm)', gym['latitude'], gym['longitude'], step_location[0], step_location[1], distance)

                    if len(gyms_to_update):
                        gym_responses = {}
                        current_gym = 1
                        status['message'] = 'Updating {} gyms for location {},{}...'.format(len(gyms_to_update), step_location[0], step_location[1])
                        log.debug(status['message'])

                        for gym in list(gyms_to_update.values()):
                            status['message'] = 'Getting details for gym {} of {} for location {},{}...'.format(current_gym, len(gyms_to_update), step_location[0], step_location[1])
                            log.debug(status['message'])
                            time.sleep(random.random() + 2)
                            response = gym_request(args, api, step_location, key_scheduler, gym)
                            status['hashuse'] += 1

                            # Make sure the gym was in range. (sometimes the API gets cranky about gyms that are ALMOST 1km away)
                            if response['responses']['GET_GYM_DETAILS']['result'] == 2:
                                log.warning('Gym @ %f/%f is out of range (%dkm), skipping', gym['latitude'], gym['longitude'], distance)
                            else:
                                gym_responses[gym['gym_id']] = response['responses']['GET_GYM_DETAILS']

                            del response
                            # Increment which gym we're on. (for status messages)
                            current_gym += 1

                        status['message'] = 'Processing details of {} gyms for location {},{}...'.format(len(gyms_to_update), step_location[0], step_location[1])
                        log.debug(status['message'])

                        if gym_responses:
                            parse_gyms(args, gym_responses, whq)
                            del gym_responses

                # Record the time and place the worker left off at.
                status['last_scan_time'] = now()
                status['location'] = step_location

                # Always delay the desired amount after "scan" completion.
                #status['message'] += ', sleeping {}s until {}'.format(args.scan_delay, time.strftime('%H:%M:%S', time.localtime(time.time() + args.scan_delay)))
                #time.sleep(args.scan_delay)

        # Catch any process exceptions, log them, and continue the thread.
        except Exception as e:
            #status['message'] = 'Exception in search_worker using account {}. Restarting with fresh account. See logs for details.'.format(account['username'])
            #
            #log.error('Exception in search_worker under account {} Exception message: {}'.format(account['username'], e))
            log.error('Exception in search_worker. Exception message: {}'.format(e))
            #account_failures.append({'account': account, 'last_fail_time': now(), 'reason': 'exception'})
            #query = (WorkerStatus
            #         .update(flag=4, last_modified=datetime.utcnow())
            #         .where(WorkerStatus.username == account['username']))
            #query.execute()
            time.sleep(args.scan_delay)


def check_login(args, account, api, position, proxy_url):

    # Logged in? Enough time left? Cool!
    if api._auth_provider and api._auth_provider._ticket_expire:
        remaining_time = old_div(api._auth_provider._ticket_expire, 1000) - time.time()
        if remaining_time > 60:
            log.debug('Credentials remain valid for another %f seconds', remaining_time)
            return

    # Try to login. (a few times, but don't get stuck here)
    i = 0
    while i < args.login_retries:
        try:
            if proxy_url:
                api.set_authentication(provider=account['auth_service'], username=account['username'], password=account['pword'], proxy_config={'http': proxy_url, 'https': proxy_url})
            else:
                api.set_authentication(provider=account['auth_service'], username=account['username'], password=account['pword'])
            break
        except AuthException:
            if i >= args.login_retries:
                raise TooManyLoginAttempts('Exceeded login attempts')
            else:
                i += 1
                #log.error('Failed to login to Pokemon Go with account %s. Trying again in %g seconds', account['username'], args.login_delay)
                time.sleep(args.login_delay)

    log.debug('Login for account %s successful', account['username'])
    time.sleep(20)


def map_request(args, api, position, key_scheduler, jitter=False):
    if args.hash_key:
        key = next(key_scheduler)
        log.debug('Using key {} for this scan.'.format(key))
        api.activate_hash_server(key)
    # Create scan_location to send to the api based off of position, because tuples aren't mutable.
    if jitter:
        # Jitter it, just a little bit.
        scan_location = jitterLocation(position)
        log.debug('Jittered to: %f/%f/%f', scan_location[0], scan_location[1], scan_location[2])
    else:
        # Just use the original coordinates.
        scan_location = position

    try:
        cell_ids = util.get_cell_ids(scan_location[0], scan_location[1])
        timestamps = [0, ] * len(cell_ids)
        req = api.create_request()
        req.get_map_objects(latitude=f2i(scan_location[0]),
                                       longitude=f2i(scan_location[1]),
                                       since_timestamp_ms=timestamps,
                                       cell_id=cell_ids)
        req.check_challenge()
        req.get_hatched_eggs()
        req.get_inventory()
        req.check_awarded_badges()
        req.download_settings()
        req.get_buddy_walked()
        response = req.call()
        response = clear_dict_response(response, True)
        return response

    except Exception as e:
        log.warning('Exception while downloading map: %s', e)
        return False


def gym_request(args, api, position, key_scheduler, gym):
    if args.hash_key:
        key = next(key_scheduler)
        log.debug('Using key {} for this scan.'.format(key))
        api.activate_hash_server(key)
    try:
        log.debug('Getting details for gym @ %f/%f (%fkm away)', gym['latitude'], gym['longitude'], calc_distance(position, [gym['latitude'], gym['longitude']]))
        req = api.create_request()
        req.get_gym_details(gym_id=gym['gym_id'],
                                player_latitude=f2i(position[0]),
                                player_longitude=f2i(position[1]),
                                gym_latitude=gym['latitude'],
                                gym_longitude=gym['longitude'])
        req.check_challenge()
        req.get_hatched_eggs()
        req.get_inventory()
        req.check_awarded_badges()
        req.download_settings()
        req.get_buddy_walked()
        x = req.call()
        x = clear_dict_response(x)
        # Print pretty(x).
        return x

    except Exception as e:
        log.warning('Exception while downloading gym details: %s', e)
        return False


def token_request(args, status, url):
    s = requests.Session()
    # Fetch the CAPTCHA_ID from 2captcha.
    try:
        captcha_id = s.post("http://2captcha.com/in.php?key={}&method=userrecaptcha&googlekey={}&pageurl={}".format(args.captcha_key, args.captcha_dsk, url)).text.split('|')[1]
        captcha_id = str(captcha_id)
    # IndexError implies that the retuned response was a 2captcha error.
    except IndexError:
        return 'ERROR'
    status['message'] = 'Retrieved captcha ID: {}; now retrieving token'.format(captcha_id)
    log.info(status['message'])
    # Get the response, retry every 5 seconds if its not ready.
    recaptcha_response = s.get("http://2captcha.com/res.php?key={}&action=get&id={}".format(args.captcha_key, captcha_id)).text
    while 'CAPCHA_NOT_READY' in recaptcha_response:
        log.info("Captcha token is not ready, retrying in 5 seconds")
        time.sleep(5)
        recaptcha_response = s.get("http://2captcha.com/res.php?key={}&action=get&id={}".format(args.captcha_key, captcha_id)).text
    token = str(recaptcha_response.split('|')[1])
    return token


def calc_distance(pos1, pos2):
    R = 6378.1  # KM radius of the earth

    dLat = math.radians(pos1[0] - pos2[0])
    dLon = math.radians(pos1[1] - pos2[1])

    a = math.sin(old_div(dLat, 2)) * math.sin(old_div(dLat, 2)) + \
        math.cos(math.radians(pos1[0])) * math.cos(math.radians(pos2[0])) * \
        math.sin(old_div(dLon, 2)) * math.sin(old_div(dLon, 2))

    c = 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))
    d = R * c

    return d


def check_speed_limit(kph, previous_location, next_location, last_scan_date):
    if kph > 0:
        move_distance = calc_distance(previous_location, next_location)
        time_elapsed = (datetime.utcnow() - last_scan_date).total_seconds()

        if time_elapsed <= 0:
            time_elapsed = 0.001

        projected_speed = 3600.0 * move_distance / time_elapsed
        log.debug('Move distance: %s k; time elapsed: %s s; Projected speed: %s kph', move_distance, time_elapsed, projected_speed)
        if projected_speed > kph:
            extra_delay = int(move_distance / kph * 3600.0 - time_elapsed) + 1
            return extra_delay

    return 0

class TooManyLoginAttempts(Exception):
    pass

