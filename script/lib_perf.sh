# Script for collecting compilation times for the standard library
# It assumes the lean binary is at the bin directory
# It assumes the programs time and realpath are available
TIME=/usr/bin/time
REALPATH=realpath

MY_PATH="`dirname \"$0\"`"
LEAN=$MY_PATH/../bin/lean
LIB=$MY_PATH/../library
for f in `find $LIB -name '*.lean'`; do
  rf=`$REALPATH $f`
  $TIME --format="$rf %e" $LEAN $rf > /dev/null
done

LIB=$MY_PATH/../hott
for f in `find $LIB -name '*.hlean'`; do
  rf=`$REALPATH $f`
  $TIME --format="$rf %e" $LEAN $rf > /dev/null
done
