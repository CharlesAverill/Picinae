for file in $(find -name "*comparison.txt"); do echo $file; grep "^False" $file; done
