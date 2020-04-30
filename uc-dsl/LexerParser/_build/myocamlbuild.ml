open Ocamlbuild_plugin


let _ = dispatch begin function
   | After_options ->
       Options.ocamlc   := S[!Options.ocamlc  ; A"-rectypes"];
       Options.ocamlopt := S[!Options.ocamlopt; A"-rectypes"];
   | _ -> ()
end

