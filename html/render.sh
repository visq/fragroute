for f in ../src/*.lhs ; do
	file=`basename ${f}`
	cat ${f} | pandoc -c http://www.haskell.org/cabal/release/cabal-latest/doc/users-guide/Cabal.css -f rst+lhs -t html+lhs > ${file/.lhs/.html}
done
cp FragRoute.html index.html