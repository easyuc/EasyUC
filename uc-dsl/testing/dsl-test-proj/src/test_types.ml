type outcome =  Failure | Empty | Success

type expr = 
| Desc of string
| Args of string list
| Outcome of outcome * string


                         

