#!/bin/sh
for FILE in ${*} ; do
	cp -f ${FILE} /tmp/x.java
	sed -e 's/part of the Green library/part of the GREEN library/' < /tmp/x.java > ${FILE}
done
