
var1="topo.csv"
var2="demand.csv"
var3="result.csv"
S=" "
echo "start"
ls test-case-all-ii/case*/| grep "test-case" | tr -d ":" |xargs -I {} echo {}
ls test-case-all-ii/case*/| grep "test-case" | tr -d ":" |xargs -I {} sh -c "./bin/future_net {}$var1 {}$var2 {}$var3 ; echo {}; cat {}$var3"
echo "end"


# ./future_net test-case-all/case600-50/case0/topo.csv test-case-all/case600-50/case0/demand.csv result.csv