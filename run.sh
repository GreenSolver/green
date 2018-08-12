#! /usr/bin/env sh
docker run 2bd4b75bb84f /bin/sh -c "git pull; ant; ant test;"
