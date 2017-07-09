//Stage 1 -- Gather pokestop and gym locations into database. Since we only need stop and gym locations currently, we can use a big (but not too big) speed limit. 120 kph should be great

runserver.py -ns -l "0.0000000, -5.000000" -np -bh -ps --db-max_connections 10 --db-threads 1 -sn RandomCityGyms -w 7 -st 10 -sl 120

//Stage 2 -- scan areas around the stops and gyms, ignore parsing gyms and stops for now to reduce database usage, we dont need to update them currently.
//Scanner will scan up to 900m from any previously found pokestop using --skip-empty and -us. you can set up some stupid huge beehive (-bh -w 2000) and it will only use the hexes within range of forts (could be 100 workers)

runserver.py -ns -l "0.0000000, -5.000000" -ng -nk --skip-empty -bh -ps --db-max_connections 50 --db-threads 40 -sn RandomCity -w 1000 -st 4

//Stage 3 -- Spawn scan and clustering for the most efficient scan pattern. Separate gyms and pokemon so you arent refreshing the gym repeatedly

runserver.py -ns -l "0.0000000, -5.000000" -ng -nk -bh -ss -clss -ps --db-max_connections 50 --db-threads 40 -sn RandomCity -w 169 -st 6
runserver.py -ns -l "0.0000000, -5.000000" -np -gi -bh -ps --db-max_connections 10 --db-threads 1 -sn RandomCityGyms -w 19 -st 3