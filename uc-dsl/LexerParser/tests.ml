open DlLexer
open DlParseTree
open DlParseFile
open TestSuite
open DlUtils

type testResult =
	| OK of testCase
	| NOK of testCase * exn option

let runTests (tests:testCase list) : testResult list =
	List.map(fun tc ->
	let res = try ignore (parse_file tc.filename); None with exn -> Some exn in
		if tc.expectedResult=res then OK tc
		else NOK (tc,res)
		) tests

let printResult (res:exn option) : unit =
	match res with
	| Some ex -> print_string "Exception>\n"; printEx ex
	| None -> print_string "No error.\n"

let printTestCase (tc:testCase) : unit =
	print_string ("\nparsing: "^tc.filename^"\n");
	print_string "Expected result: ";
	printResult tc.expectedResult

let printTestResult (tr:testResult) : unit =
	match tr with
	| OK tC -> printTestCase tC; print_string "\nPASSED.\n\n"
	| NOK (tC,res) -> printTestCase tC; print_string "\nFAILED! The actual result was:\n\n"; printResult res

let printSummary (trl:testResult list) : unit =
	let passNo = List.length (List.filter (fun tr -> match tr with OK tC ->true|_->false) trl) in
	let tcNo = List.length trl in
	print_string ("\nPASSED:"^(string_of_int passNo)^"/FAILED:"^(string_of_int (tcNo-passNo))^"\n")

let printTestResults (trl:testResult list) : unit =
	List.iter printTestResult trl;
	printSummary trl
 
(*TODO make all tests contain only one error so the order of checks doesn't change the outcome*)

let tests = printTestResults (runTests suite);
