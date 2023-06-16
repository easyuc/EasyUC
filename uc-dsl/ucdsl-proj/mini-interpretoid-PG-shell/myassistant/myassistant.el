;; myassistant.el

(defun uc-file-frame (str)
  "Open a new frame with a buffer named *UC file*.
insert contents from a file, mark the positions between character positions"
  (save-excursion ;we need save excursion as otherwise PG gets confused parsing the shell output
    (switch-to-buffer-other-frame "*UC file*")
    (let ( (uc-file-line (car (split-string str ";")))
           (prefix "UC file position: ")
         )
      (let ( (params-line  (substring uc-file-line (length prefix)))
           )
        (let ((params (split-string params-line)))
          (let ( (filenam    (nth 0 params))
                 (ch-pos-beg (string-to-number (nth 1 params)))
                 (ch-pos-end (string-to-number (nth 2 params)))
               )
            (erase-buffer)
            (insert-file filenam)
            (let ((x (make-overlay ch-pos-beg ch-pos-end)))
              (overlay-put x 'face '(:foreground "blue")))
          )
        )
      )
    )
  )
)
  
(defun frame-with-uc-file (cmd str)
  "call empty-frame if myassist shell output starts with UC file position:"
  (if (string-prefix-p "UC file position:" string)
      (uc-file-frame str)
;;    (save-excursion (switch-to-buffer-other-frame "*UC file*"))
  )
)
  
(require 'proof) ;; sets some default values

(require 'proof-easy-config)		; easy configure mechanism

(
 proof-easy-config 'myassistant "MyAssistant"
 proof-prog-name		"myassist"
 
 proof-terminal-string		"."
 
 proof-script-comment-start	"(*"
 proof-script-comment-end	"*)"
 
 proof-goal-command-regexp	"^load"
 proof-save-command-regexp	"^done"

 
 proof-goal-command		"load %s."
 proof-save-command		"done."
 
 proof-shell-start-goals-regexp	 "^state:"
 proof-shell-end-goals-regexp	 ";"
 
 proof-shell-quit-cmd		 "done."
 proof-assistant-home-page	 "http://yes"
 proof-shell-annotated-prompt-regexp "^>"
 proof-shell-error-regexp	 "^Error:"
 
 proof-shell-handle-output-system-specific 'frame-with-uc-file
)

(provide 'myassistant)

;;; myassistant.el ends here
