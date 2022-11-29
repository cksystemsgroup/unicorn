#/bin/bash

/usr/bin/time -p -f '%e' ${@:1} 2>&1 | tail -n 1
