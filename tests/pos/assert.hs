assert as {safe:Bool | safe == True} -> Unit
assert = 0

foo :: {zero:Int | zero == 0} -> Unit
foo = \z -> assert (z==0)
