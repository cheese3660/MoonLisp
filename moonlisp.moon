class Number
		new: (num)=>
				@num = num
		__call: (num)=>
				unless num
						return @num
				@num = num
class Symbol
		new: (name) =>
				@name = name
		__call: (name)=>
				unless name
						return @name
				@name = name
class List
		new: (expList) =>
				@expList = expList
		__call: (expList)=>
				unless expList
						return @expList
				@expList = expList
class String
		new: (str) =>
				@str = str
		__call: (str) =>
				unless str
					return @str
				@str = str
class Environment
		@zip: (parmT={},argT={}) =>
			return {v,argT[k] for k,v in ipairs(parmT)}
		new: (parms={},args={},outer=nil) =>
				@update(@@zip(parms,args))
				@outer= outer
		update: (tab) =>
				for k,v in pairs(tab)
						@[k] = v
		find: (k) =>
				if @[k] ~= nil
						--print("Inside self")
						return @
				elseif self.outer
						--print("Looking shallower")
						return self.outer\find(k)
				else
						--if nothing has it return the global_env, it will be nil, can be used to set a variable in the global_env
						return @
class Procedure
		@eval: nil
		@serialize: nil
		@MoonLisp: nil
		@lastCall: ""
		new: (parms, body, env) =>
				@parms, @body, @env = parms, body, env
		__call: (...) =>
				--print(@@lastCall.." IS BEING CALLED WITH ARGS: ",...)
				--print("Serialization of environment")
				--@@MoonLisp\serialize(@@MoonLisp.Environment(@parms,table.pack(...),@env))
				return @@MoonLisp\eval(@body, @@MoonLisp.Environment(@parms,table.pack(...),@env))
class Nil
		new: =>
		__call: =>
				return nil
standard_env = () ->
		env = Environment()
		env\update(math) --brings all the math functions and constants in
		env\update(table)
		env\update({
				['+']: (a,b)->
						a+b
				['-']: (a,b)->
						unless b
								return -a
						a-b
				['*']: (a,b)->
						a*b
				["/"]: (a,b)->
						a/b
				["^"]: (a,b)->
						a ^ b
				["&"]: (a,b)->
						a & b
				["|"]: (a,b)->
						a | b
				["~"]: (a,b)->
						unless b
								return ~a
						ana = ~a
						bnb = ~b
						anb = ~(ana & b)
						bna = ~(bnb & a)
						return ~(anb & bna)
				[">>"]: (a,b)->
						a >> b
				["<<"]: (a,b)->
						a << b
				["phi"]: (1+math.sqrt(5))/2
				["print"]: (strl)->
						print(strl)
				["write"]: (strl)->
						io.write(strl)
				["writenum"]: (num)->
						io.write(num)
				["printnum"]: (num)->
						print(num)
				["readnum"]: ()->
						return tonumber io.read!
				["readstring"]: ()-> --uses something akin to c strings
						return io.read!
				[">"]: (a,b)->
						a>b
				["<"]: (a,b)->
						a<b
				[">="]: (a,b)->
						a>=b
				["<="]: (a,b)->
						a<=b
				["="]: (a,b)->
						a==b
				["e"]: math.exp(1)
				["begin"]: ()->
						return nil
				["map"]: (proc,list)->
						[proc(v) for v in list]
				["range"]: (a,b) ->
						[i for i = a,b]
				["range_when"]: (a,b,proc) ->
						[i for i = a,b when proc(i)]
				["not"]: (a) ->
						return not a
				["push"]: (list,val) ->
						table.insert(list,val)
				["pop"]: (list) ->
						table.remove(list,val)
				["procedure?"]: (val) ->
						type(val) == Procedure
				["number?"]: (val) ->
						type(val) == "number"
				["list?"]: (val) ->
						type(val) == "table"
				["length"]: (val) ->
						#val
				["exit"]: (val) ->
						os.exit(val)
				["error"]: (list) ->
						error(list)
				["copy"]: (list) ->
						return [item for item in *list]
				["copy-dict"]: (dict) ->
						return {k,v for k,v in pairs(dict)}
				["dict!"]: () ->
						return {}
				["dict-set!"]: (dict, k, v) ->
						dict[k] = v
				["dict-get"]: (dict, k) ->
						dict[k]
				["pairs"]: (dict, func) ->		--returns a list which is a map of func onto dict
						{k,func(k,v) for k,v in pairs(dict)}
				["[]"]: (dict, k, v) ->
						if v == nil
								return dict[k]
						else
								dict[k] = v
				["mt"]: (dict,dict2) ->
						if dict2 == nil
								return getmetatable(dict)
						else
								setmetatable(dict,dict2)
				["nil?"]: (a) ->
						a == nil
				["exists?"]: (a) ->
						a ~= nil
				["and"]: (a,b) ->
						a and b
				["or"]: (a,b) ->
						a or b
				["xor"]: (a,b) ->
						a or b and not (a and b)
				["true"]: true
				["false"]: false
		})
		return env
class MoonLisp
		@global_env: standard_env!
		@Procedure: Procedure
		@Number: Number
		@Symbol: Symbol
		@Environment: Environment
		@List: List
		@Nil: Nil
		@procedure_call: false
		@standard_env: nil
		@recursion: {}
		@String: String
		@isArray: (t) =>
				i = 0
				for _ in pairs(t) do
						i+= 1
						if t[i] == nil then return false
				return true
		@isRecursed: (t) =>
				for item in *@.recursion
					if item == t
						return true
				return false
		@removeRecursion: (t) =>
				for i = 1, #@.recursion
					if @.recursion[i] == t
						table.remove(@.recursion,i)
						break
		@getType: (item) =>
				switch type(item)
						when @.Procedure
								return "Procedure"
						when @.Number
								return "Number"
						when @.Symbol
								return "Symbol"
						when @.List
								return "List"
						when @.Environment
								return "Environment"
						when @.Nil
								return "Nil"
						when @.String
								return "String"
						else
								return type(item)
		@split: (str) =>
				tokens = {}
				token_i = 1
				c_token = ""
				in_quote = false
				escaped = false
				in_comment = false
				for c in str\gmatch'.' do
						unless in_comment
								if c == '(' or c == ')'
										unless escaped
												unless c_token == ""
														tokens[token_i] = c_token
														c_token = ""
														token_i += 1
												tokens[token_i] = c
												token_i += 1
												continue
										else
												escaped = false
								elseif c == '\\'
										unless escaped
												escaped = true
												continue
										else
												escaped = false
								elseif c\match("%s")
										unless in_quote
												unless c_token == ""
														tokens[token_i] = c_token
														c_token = ""
														token_i += 1
												continue
								elseif c == '"'
										unless escaped
												if not in_quote
														unless c_token == ""
																tokens[token_i] = c_token
																c_token=""
																token_i+=1
												if in_quote
														tokens[token_i] = '"'..c_token..'"'
														c_token = ""
														token_i += 1
												in_quote = not in_quote
												escaped = false
												continue
								elseif c == 'n'
										if escaped
												escaped = false
												c_token ..= '\n'
												continue
								elseif c == ';'
										unless escaped or in_quote
												escaped = false
												in_comment = true
												continue
								c_token ..= c
						else
								if c == '\n'
										in_comment = false
				unless c_token == ""
						tokens[token_i] = c_token
				return tokens
		@tokenize: (chars) =>
				return @\split(chars)
		@parse: (prog) =>
				return @\create_tokens_table(@\tokenize(prog))
		@create_tokens_table: (tokens)=> --to allow for more than 1 
				tokens_table = {}
				token_i = 1
				while #tokens > 0 do
						cur_table = {}
						pars = 0
						started = true
						while pars > 0 or started
								started = false
								cur_token = table.remove(tokens,1)
								if not cur_token then
										error("SyntaxError: unexpected EOF")
								if cur_token == "("
										pars += 1
								elseif cur_token == ")"
										pars -= 1
										if pars < 0
												error("SyntaxError: unexpected )\nAt Token:"..token_i)
								table.insert(cur_table,cur_token)
								token_i+=1
						table.insert(tokens_table,@\read_from_tokens(cur_table))
				return tokens_table

		@read_from_tokens: (tokens) =>
				if #tokens == 0
						error("SyntaxError: unexpected EOF")
				token = table.remove(tokens,1)
				if token == '('
						L = {}
						while tokens[1] != ')'
								table.insert(L,@\read_from_tokens(tokens))
						table.remove(tokens,1)
						return @.List(L)
				elseif token == ')'
						error("SyntaxError: unexpected )")
				elseif token == ' '
						return @\read_from_tokens(tokens)
				else
						return @\atom(token)
		@atom: (token) =>
				if token\sub(1,1) == '"' and token\sub(-1,-1) == '"'
						return @.String(token\sub(2,-2))
				elseif token == "nil"
						return @.Nil!
				elseif tonumber(token)
						return @.Number(tonumber(token))
				else
						return @.Symbol(token)
		@eval: (x,env=@.global_env) =>
				--int(@\prettyPrint(x))
				if type(x) == 'table'
						local last
						for exp in *x do
								last,returning,breaking = @\eval(exp,env)
								if returning or breaking
										return last,returning,breaking
						return last, false
				else
						bodyStr = ""
						genBody = (body) ->
								if type(body) == @.Number
										bodyStr ..= body!
								elseif type(body) == @.Symbol
										bodyStr ..= '"'..body!\gsub("\"","\\\"")\gsub("%(","\\(")\gsub("%)","\\)")..'"'
								elseif type(body) == @.Nil
										bodyStr ..= 'nil'
								elseif type(body) == @.List
										bodyStr ..= '('
										for item in *body!
												genBody(item)
												unless _index_0 == #_list_0 --EXTREME MOONSCRIPT HAX
														bodyStr ..= ' '
										bodyStr ..= ')'
						genBody(x)
						--print(bodyStr)
				if type(x) == @.Number
						--print("Number")
						return x!,false,false
				elseif type(x) == @.Symbol
						if @procedure_call
								@.Procedure.lastCall = x!
						thing= env\find(x!)[x!]
						return thing,false,false
				elseif type(x) == @.Nil
						return x!,false,false
				elseif type(x) == @.String
						return x!,false,false
				elseif type(x) == @.List
						list = x!
						if #list == 0
								return nil,false
						op = list[1]!
						if op == "list"
								--print("List Creation"),false
								result = {}
								returning = false
								--make a list from a list of expressions
								for exp in *list[2,] do
										val, returning,breaking = @\eval(exp,env)
										if returning or breaking
											return val,returning,breaking
								return result,false,false
						elseif op == "return"
								return @\eval(list[2],env),true,false
						elseif op == "break"
								return nil,false,true
						elseif op == "global"
								symbol = list[2]!
								exp = list[3]
								res = @\eval(exp,env)
								@.global_env[symbol] = res
								return nil,false,false
						elseif op == "define"
								--print("Definition")
								symbol = list[2]!
								exp = list[3]
								res = @\eval(exp,env)
								
								env[symbol] = res --definition and assignment skip returns
								return nil,false,false
						elseif op == "set!"
								--print("Assignment")
								symbol = list[2]!
								exp = list[3]
								res = @\eval(exp,env)
								env\find(symbol)[symbol] = res
								return nil,false,false
						elseif op == "if"
								--print("Condition")
								--@\prettyPrint env
								test = list[2]
								conseq = list[3]
								alt = list[4]
								exp = alt
								if @\eval(test,env) 
										exp = conseq
								return @\eval(exp,@.Environment(nil,nil,env))
						elseif op == "pretty-print"
								serializand = @\eval(list[2],env) --so does serialization
								@\prettyPrint(serializand)
								return nil,false,false
						elseif op == 'lambda' or op == 'λ'
								--print("Lambda")
								if type(list[2]) ~= @.List
										error("Arguments in a lambda should be a list\nnot a "..@\getType(list[2]))
								parms = list[2]!
								parms = [item! for item in *parms]
								body = list[3]
								return @.Procedure(parms,body,env),false,false
						elseif op == 'string'
								if type(list[2]) ~= @.Symbol
										error("Arguments in a call to string should be a Symbol\nnot a "..@\getType(list[2]))
								list = list[2]!
								return list,false,false
						elseif op == 'exp-list' or op == '!' --makes it possible to chain
								local res
								for exp in *list[2,-1]
										res,returning,breaking = @\eval(exp,env)
										if returning or breaking
												return res,returning,breaking
								--print("On Last")
								return @\eval(list[#list],env)
						elseif op == 'load' --loads a string and returns a procedure
								loadStr = @\eval(list[2],env)
								body = @\parse(loadStr)
								return @.Procedure({},body,env)
						elseif op == 'get-body' --returns the body of a procedure as a string, useful for creating your own serialization
								proc = @\eval(list[2],env) --immune to returns
								if type(proc) ~= @.Procedure then
										print(proc)
										error("The argument to get body has to be a procedure\nNot a "..type(proc))
								bodyStr = ""
								genBody = (body) ->
										if type(body) == @.Number
												bodyStr ..= body!
										elseif type(body) == @.Symbol
												bodyStr ..= '"'..body!\gsub("\"","\\\"")\gsub("%(","\\(")\gsub("%)","\\)")..'"'
										elseif type(body) == @.Nil
												bodyStr ..= 'nil'
										elseif type(body) == @.List
												bodyStr ..= '('
												for item in *body!
														genBody(item)
														unless _index_0 == #_list_0 --EXTREME MOONSCRIPT HAX
																bodyStr ..= ' '
												bodyStr ..= ')'
								genBody(proc.body)
								bodyStr,false,false
						elseif op == 'quote' --returns the token list
								return list[2],false,false
						elseif op == 'serialize-func'
								proc = @\eval(list[2],env) --immune to returns
								if type(proc) ~= @.Procedure then
										print(proc)
										error("The argument to get body has to be a procedure\nNot a "..type(proc))
								bodyStr = ""
								genBody = (body) ->
										if type(body) == @.Number
												bodyStr ..= body!
										elseif type(body) == @.Symbol
												bodyStr ..= '"'..body!\gsub("\"","\\\"")\gsub("%(","\\(")\gsub("%)","\\)")..'"'
										elseif type(body) == @.Nil
												bodyStr ..= 'nil'
										elseif type(body) == @.List
												bodyStr ..= '('
												for item in *body!
														genBody(item)
														unless _index_0 == #_list_0 --EXTREME MOONSCRIPT HAX
																bodyStr ..= ' '
												bodyStr ..= ')'
								genBody(proc.body)
								argStr = '('
								for v in *proc.parms
										argStr ..= '"'..v\gsub("\"","\\\"")\gsub("%(","\\(")\gsub("%)","\\)")..'"'
										unless _index_0 == #_list_0 --AGAIN EXTREME MOONSCRIPT HAX
												argStr ..= ' '
								argStr ..= ')'
								procStr = '(lambda '..argStr..' '..bodyStr..')'
								procStr,false,false
						elseif op == 'serialize'
								bodyStr = ''
								genBody = (body) ->
										if type(body) == @.Number
												bodyStr ..= body!
										elseif type(body) == @.Symbol
												bodyStr ..= '"'..body!\gsub("\"","\\\"")\gsub("%(","\\(")\gsub("%)","\\)")..'"'
										elseif type(body) == @.Nil
												bodyStr ..= 'nil'
										elseif type(body) == @.List
												bodyStr ..= '('
												for item in *body!
														genBody(item)
														unless _index_0 == #_list_0 --EXTREME MOONSCRIPT HAX
																bodyStr ..= ' '
												bodyStr ..= ')'
								genBody @\eval(list[2],env)
								return bodyStr
						elseif op == 'require' --requires a lua library to the global environment
								name = @\eval(list[2],env)
								lib_base = dofile(name..'.lua')
								lib = {name..'-'..k,v for k,v in pairs(lib_base)}
								@.global_env\update(lib)
								@.global_env[name] = lib_base --for libraries that call functions from themselves
						elseif op == 'inEnv'
								print("Changing environment")
								list = @\eval(list[2],env)
								env2 = Environment()
								env2\update(list) --if the list has an outer, the one in the environment will be replaced
								return @\eval(list[3],env2)
						elseif op == 'globalEnv'
								return @.global_env
						elseif op == 'currentEnv'
								return env
						elseif op == 'resetEnv' --if you are in the global env this will kill it
								env = Environment(nil,nil,env.outer)
						elseif op == 'standardEnv'
								return @.standard_env!
						elseif op == 'switchEnv' --will switch the environment, even the outer ones
								list = @\eval(list[2],env)
								env = Environment()
								env\update(list)
						elseif op == 'switchGlobalEnv'
								list = @\eval(list[2],env)
								@.global_env = Environment()
								@.global_env = env\update(list)
						else
								--@\prettyPrint(env)
								@procedure_call = true
								proc = @\eval(list[1],env)
								@procedure_call = false
								if type(proc) ~= @.Procedure
									unless type(proc) == "function"
										@\prettyPrint(proc)
										error("Procedure: "..@.Procedure.lastCall.." is a "..@\getType(proc))
								if not proc
									error("Procedure: "..@.Procedure.lastCall.." does not exist")
								vals = [@\eval(arg,env) for arg in *list[2,]]
								--io.write("Args: ")
								--print(table.unpack(vals))
								--print(proc(table.unpack(vals)))
								res = proc(table.unpack(vals))
								return res
		@prettyPrint: (body, indent=0) =>
				--error("Printing")
				if indent==0
					@.recursion = {}
				io.write(string.rep("\t",indent))
				if type(body) == @.List
						print("List")
						for item in *body!
								@\prettyPrint(item,indent+1)
				elseif type(body) == @.Procedure
						print("Procedure")
						io.write(string.rep("\t",indent))
						io.write("\tArgs: ")
						for item in *body.parms
								io.write(item..' ')
						io.write('\n'..string.rep("\t",indent))
						print("\tBody")
						@\prettyPrint(body.body,indent+2)
				elseif type(body) == @.Number or type(body) == @.Symbol
						print(@\getType(body)..": "..body!)
				elseif type(body) == "table"
						table.insert(@.recursion,body)
						if @\isArray(body)
								print("Array")
								for item in *body
										unless @\isRecursed(item)
											@\prettyPrint(item,indent+1)
										else
											io.write(string.rep("\t",indent+1))
											print("Recursion")
						else
								print("Dictionary")
								for k,v in pairs(body)
										unless @\isRecursed(v)
												io.write(string.rep("\t",indent+1))
												print(k)
												@\prettyPrint(v,indent+2)
										else
												io.write(string.rep("\t",indent+1))
												print(k..": recursion")
						@\removeRecursion(body)
				elseif type(body) == "function"
						print("Function")
				elseif type(body) == @.Environment
						table.insert(@.recursion,body)
						print("Environment")
						for k,v in pairs(body)
								unless @\isRecursed(v)
									io.write(string.rep("\t",indent+1))
									print(k)
									@\prettyPrint(v,indent+2)
								else
									io.write(string.rep("\t",indent+1))
									print(k..": recursion")
						@\removeRecursion(body)
				elseif type(body) == @.String
						print("String: "..body!)
				else
						io.write(@\getType(body)..': ')
						print(body)
MoonLisp.Procedure.eval = MoonLisp.eval
Procedure.eval = MoonLisp.eval
MoonLisp.Procedure.serialize = MoonLisp.serialize
Procedure.serialize = MoonLisp.serialize
MoonLisp.Procedure.MoonLisp = MoonLisp
Procedure.MoonLisp = MoonLisp
MoonLisp.standard_env = standard_env
return MoonLisp