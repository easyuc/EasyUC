;; ucInterpreter.el

;;Setup:
;;1.
;;create  /ucInterpreter folder in the proof-general folder 
;;
;;2.
;;add line
;;(ucInterpreter "UCInterpreter" "uci")
;;to proof-site.el inside proof-general folder /generic
;;
;;3.
;;Add the folder that contains ucInterpreterClient.exe
;;to the $PATH env variable, e.g. by running in shell:
;;export PATH=$PATH:/usr/local/share/easycrypt/EasyUC/uc-dsl/ucdsl-proj/_build/default/src/
;;
;;Also add this path to the exec-path in .emacs file, e.g.:
;;(setq exec-path
;;        (append
;;         '("/usr/local/share/easycrypt/EasyUC/uc-dsl/ucdsl-proj/_build/default/src/")
;;         exec-path))
;;
;;4.
;;run emacs, then
;;M-x byte-recompile-directory RET ~/.emacs.d/elpa/
;;to recompile proof-site.el
;;
;;5.
;;close emacs, run emacs again, then
;;M-x ucInterpreter-mode
;;alternatively, run "emacs filename.uci" to start with  
;;.uci script for ucInterpreter 


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

;;error highlighting adapted from easycrypt.el

(defun get-last-error-location ()
  "Remove [error] in the error message and extract the position and
length of the error."
  (proof-with-current-buffer-if-exists proof-response-buffer

     (goto-char (point-max))
     (when (re-search-backward "\\[error:\\([0-9]+\\)-\\([0-9]+\\)\\]" nil t)
        (let* ((inhibit-read-only t)
               (pos1 (string-to-number (match-string 1)))
               (pos2 (string-to-number (match-string 2)))
               (len (- pos2 pos1)))

              (delete-region (match-beginning 0) (match-end 0))
              (list pos1 len)))))

(defun advance-until-command ()
   (while (proof-looking-at "\\s-") (forward-char 1)))

(defun highlight-error ()
  "Use ‘get-last-error-location’ to know the position of the
error and then highlight in the script buffer."
  (proof-with-current-buffer-if-exists proof-script-buffer
    (let ((mtch (get-last-error-location)))
        (when mtch
          (let ((pos (car mtch))
                  (lgth (cadr mtch)))
          ;;(if (eq (proof-unprocessed-begin) (point-min))
                (goto-char (proof-unprocessed-begin))
          ;;      (goto-char (+ (proof-unprocessed-begin 1)))
          ;;    )
            (advance-until-command)
             (goto-char (+ (point) pos))
             (span-make-self-removing-span
               (point) (+ (point) lgth)
               'face 'proof-script-highlight-error-face))))))

(defun highlight-error-hook ()
  (highlight-error))

(require 'proof-easy-config)		; easy configure mechanism

(
 proof-easy-config 'ucInterpreter "UCInterpreter"
 proof-prog-name		"ucInterpreterClient.exe"
 
 proof-terminal-string		".\n"
 
 proof-script-comment-start	"(*"
 proof-script-comment-end	"*)"
 
 proof-goal-command-regexp	"load"
 proof-save-command-regexp	"finish"


 proof-non-undoables-regexp     "back"
 proof-undo-n-times-cmd         "back %s.\n"
 
 proof-goal-command		"load %s.\n"
 proof-save-command		"finish.\n"
 
 proof-shell-start-goals-regexp	 "state:"
 proof-shell-end-goals-regexp	 ";"
 
 proof-shell-quit-cmd		 "quit.\n"
 proof-assistant-home-page	 "http://yes"
 proof-shell-annotated-prompt-regexp "#[0-9]*>"
 proof-shell-error-regexp	 "^\\[error:"
 
 proof-shell-handle-output-system-specific 'frame-with-uc-file

 proof-shell-handle-error-or-interrupt-hook 
  'highlight-error-hook

 ;;proof-general-debug "non-nil thing"
)

(provide 'ucInterpreter)

;;; ucInterpreter.el ends here
