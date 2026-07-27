Use the updated four-variable reduction instead:

  python exact_self_loop_z3.py 13 --margin 1 --substitute-active --reduce-triple --split 2 --box-timeout-ms 60000
  python exact_self_loop_z3.py 14 --margin 1 --substitute-active --reduce-triple --split 2 --box-timeout-ms 60000

  For support 7, the replacement test is:

  python exact_self_loop_z3.py 7 --weight 3/4,1,1,1 --margin 1/10 --substitute-active --reduce-triple --split 2 --box-timeout-ms 60000

  You’ll need the updated local script; the old version lacks --reduce-triple.
