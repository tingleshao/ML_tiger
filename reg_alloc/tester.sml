CM.make "sources.cm";

(*((if OS.FileSys.isDir("testcases_out") = false
then OS.FileSys.mkDir("testcases_out")
else ())
handle SysErr => OS.FileSys.mkDir("testcases_out"));
*)
fun tester () =
let
	val dir = "../pos_tests/"
	val outdir = "../build/"

	(*fun parse_file (fname:string) =
	let
	(*	val a = TextIO.openOut ("testcases_out/" ^ fname ^ ".AST") *)
	(*	val absyn = Parse.parse ("../pos_tests/" ^ fname) *)
	in
	(*	PrintAbsyn.print (a,absyn); *)
	print (fname ^ ":\n");
	(*	(print (" IR: "^Translate.exp_to_str(
	#exp2 (Semant.transProg absyn))^"\n")); *)

	(Main.compile (fname,"foo"));
	()
	end
	handle Empty => print ("Empty Exception raised in: "^fname^"\n")
	| _  => print ("Unknown exception raised in: "^fname^"\n") *)
	fun parse_dir (s) = 
	let 
		val ds = OS.FileSys.openDir (s)
		fun loop (ds) = (
		case OS.FileSys.readDir (ds) of 
			NONE => [] before OS.FileSys.closeDir (ds)
			| file => file::loop (ds))
		in
			loop (ds) handle e => (OS.FileSys.closeDir (ds); raise (e))
		end
		fun test_file ([]) = print "\n"
		| test_file (h::s) = 
		let val infile = dir ^ (valOf(h))
			val outfile = outdir  ^ (valOf(h)) ^ ".s"
		in 
			(print (infile ^ "\n");
			Main.compile(infile,outfile) handle e => ();
			test_file(s)
			)
		end
	in
		test_file (parse_dir(dir))
	end;

	tester ();
