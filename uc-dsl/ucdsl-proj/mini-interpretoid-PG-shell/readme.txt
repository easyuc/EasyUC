Setup:
1.
copy /myassistant folder into proof-general folder 

2.
add line
(myassistant "MyAssistant" "myasst")
to proof-site.el inside proof-general folder /generic

3.
compile my assistant by running
ocamlc -o myassist myassist.ml
in /myasscode folder

4.
Add /myasscode to the $PATH env variable, e.g. by running in shell:
export PATH=$PATH:~/.emacs.d/elpa/proof-general-20230407.909/myassistant/myasscod

5.
run emacs, then
M-x byte-recompile-directory RET ~/.emacs.d/elpa/
to recompile proof-site.el

6.
close emacs, run emacs again, then
M-x myassistant-mode
alternatively, run "emacs demo.myasst" in ~/.emacs.d/elpa/proof-general-20230407.909/myassistant folder to start with the demo script for myassistant


How it works:
myassist.ml contains ocaml code for a shell client.
The client is very simple, it expects that the input from stdin ends with "." and that the first input is "load filename."
The filename is the name of the file to be loaded, e.g. loremipsum is a file provided with the demo.
Then one can write any number of commands (ending with ".")
After a command is entered, the client will respond by either writing an error message on stdout
(in case the first command is not "load", or the input doesn't end with ".")
or, if the command is OK, then two things are printed out.
First, a line that points to the region (a pair of character positions) in the file that was loaded.
Second, a line that outputs state (an integer).
After each command, the region is set to be between positions state and 2*state, and the state is incremented by one.
If the command "done." is issued, the client expects another file to be loaded.
Once the command "quit." is issued the client exits.

myassistant.el contains elisp code that sets up Proof General to work with this shell client.
Everything from the first command (load) to last command (done) is considered to be one goal/lemma.
Inputs for the client are shown in the script buffer.
The state is shown in the goal buffer. 
Errors are shown in the response buffer.
The line that points to the region within the loaded file is not shown in Proof General's buffers,
instead, the file is shown in an additional frame, with the text inside the region colored blue. 
