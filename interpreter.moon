files = {...}
file = files[1]
require"moon.all"
Expression = dofile"moonlisp.lua"
repl = (label, env) ->
		print("Moon Lisp V1.0")
		while true do
				io.write(label.." ")
				expr=  io.read()
				if expr == 'exit'
						print("Exiting...")
						return 0
				if expr\sub(1,1) == '='
						Expression\serialize(Expression\parse(expr\sub(2,-1)))
						continue
				result = Expression\eval(Expression\parse(expr))
				print(result)
unless file
		repl("MoonLisp:")
else
		f = assert(io.open(file, "rb"))
		content = f\read("*a")
		f\close()
		Expression\eval(Expression\parse(content))