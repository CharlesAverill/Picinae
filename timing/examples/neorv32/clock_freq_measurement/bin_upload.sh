#!/bin/sh
# https://www.dannysung.com/articles/linux/tips/sending-binary-files-via-minicom/
INFILE=/dev/null
OUTFILE=/dev/null

while [ $# -gt 0 ]; do
 case "$1" in
 -i)
 shift
 INFILE="$1"
 ;;
 -o)
 shift
 OUTFILE="$1"
 ;;
 -h|--help)
 echo "$0 -i infile -o outfile"
 ;;
 *)
 INFILE="$1"
 esac
 shift
done
cat << EOF
binary-xfer utility for minicom
Sending file ${INFILE} to ${OUTFILE}
EOF

/usr/bin/pv --force -i 0.25 -B 128  ${INFILE}  2>&1 > ${OUTFILE}
# Use the line below if you don't have pv!

# /bin/cat ${INFILE} > ${OUTFILE}
cat << EOF

File transfer complete
EOF
sleep 1
