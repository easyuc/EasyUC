type outcome =  Failure | Unknown | Empty | Success

type expr = 
| Desc of string
| Args of string list
| Outcome of outcome * string


                         

