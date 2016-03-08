#!/bin/bash

echo -e "\033[0;32mChecking Implications.\033[0m\n"
for ctl_file in `ls fse2016/*.ctl`; do
    echo -e "\033[0;34m $ctl_file \033[0m\n"
    time -p timeout 3h ./implication-checker $ctl_file-expected $ctl_file-obtained #> $ctl_file.out
done

echo -e "\033[0;32mDone.\033[0m\n"
