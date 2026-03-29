rm -rf work

# previous clean.sh, without it we would be copying old .git dirs and get a test failure
rm -rf DiamondExample-*/.git
rm -rf DiamondExample-*/.lake DiamondExample-*/lake-manifest.json
rm -f DiamondExample-D/produced.out
