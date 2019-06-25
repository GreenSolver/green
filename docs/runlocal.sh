#!/bin/sh

./copyapi.sh \
&& rm -rf /tmp/site-green \
&& bundle exec jekyll serve --port 4040 --destination /tmp/site-green

