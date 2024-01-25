;; ucdsl-interpreter.el

;;Setup:
;;1.
;;create  /ucdsl-interpreter folder in the proof-general folder 
;;
;;2.
;;add line
;;(ucdsl-interpreter "UC DSL Interpreter" "uci")
;;to proof-site.el inside proof-general folder /generic
;;
;;3.
;;Add this path to the exec-path in .emacs file, e.g.:
;;(setq exec-path
;;        (append
;;         '("/usr/local/share/easycrypt/EasyUC/uc-dsl/bin/")
;;         exec-path))
;;
;;4.
;;run emacs, then
;;M-x byte-recompile-directory RET ~/.emacs.d/elpa/
;;to recompile proof-site.el
;;
;;5.
;;close emacs, run emacs again, then
;;M-x ucdsl-interpreter-mode
;;alternatively, run "emacs filename.uci" to start with  
;;.uci script for ucdsl-interpreter
(defvar uc-frame)
(defvar uc-window)
(defvar uc-buffer)
(defvar is-uc-frame-initialized nil)

(defun init-uc-file-frame ()
  "create a new, invisible frame with name *UC file*, create a buffer called uc-file-buffer, set it as a buffer for frame's window and set uc-frame/window/buffer variables for future reference"
  (if (eq is-uc-frame-initialized nil)
    (progn	
      (setq uc-frame (make-frame '((name . "*UC file*") (visibility . nil))))
      (setq uc-window (frame-selected-window uc-frame))
      (setq uc-buffer (generate-new-buffer "uc-file-buffer"))
      (set-window-buffer uc-window uc-buffer)
      (with-current-buffer uc-buffer
        (ucdsl-mode)
        (setq buffer-read-only t)
	)
      (setq is-uc-frame-initialized t)
    )
  )
)



(defun uc-file-frame (str)
  "If uc file and location in it are provided, insert file contents into uc-buffer from a file, mark the positions between character positions of the location.
If not, hide the uc-frame "
  (with-selected-frame uc-frame;;uc-window ;;uc-buffer
    (let ( (uc-file-line (car (split-string str ";")))
           (prefix "UC file position: ")
         )
      (let ( (params-line  (substring uc-file-line (length prefix)))
             (inhibit-read-only t)
             )
	(make-frame-visible)
	(with-selected-window uc-window
	(with-current-buffer uc-buffer
          (erase-buffer)
          (if (string= params-line "None")            ;if
            (progn                                    ;then 
             (insert "*** no code running ***")
             (set-frame-name "*UC file*")
            ) 
            (let ((params (split-string params-line)));else
              (let ( (filenam    (nth 0 params))
                     (ch-pos-beg (string-to-number (nth 1 params)))
                     (ch-pos-end (string-to-number (nth 2 params)))
                   )
                (insert-file filenam)
                (set-frame-name filenam)
                (let ((x (make-overlay ch-pos-beg ch-pos-end)))
                  (overlay-put x 'face '(:background "sky blue")))
              ;;(auto-raise-mode -1)
              ;;(set-mark ch-pos-beg)
              ;;(activate-mark)
                (goto-char ch-pos-end)
                (goto-char ch-pos-beg)
	      )
            )
          )
        ))
      )
    )
  )
)

(require 'cl)
  
(defun frame-with-uc-file (cmd str)
  "call empty-frame if ucdsl-interpreter shell output starts with UC file position:"
  ;;(proof-debug (concat "frame-with-uc-file of " str))
  (init-uc-file-frame)
  (let ((stps (search "UC file position:" str)))
    (if (and stps (member uc-frame (frame-list))) 
      (uc-file-frame (substring str stps nil))
;;    (save-excursion (switch-to-buffer-other-frame "*UC file*"))
    )
  )
)


(setq proof-buffer-menu 
  (cons "Buffers"
	`(["Layout Windows" proof-layout-windows]
	  ,proof-3-window-mode-policy
	  ""
	  ["Rotate Output Buffers"
	   proof-display-some-buffers
	   :visible (not proof-three-window-enable)
	   :active (buffer-live-p proof-goals-buffer)]
	  ["Clear Responses"
	   pg-response-clear-displays
	   :active (buffer-live-p proof-response-buffer)]
	  "----"
	  ["Active Scripting"
	   (proof-switch-to-buffer proof-script-buffer)
	   :active (buffer-live-p proof-script-buffer)]
	  ["Configuration"
	   (proof-switch-to-buffer proof-goals-buffer t)
	   :active (buffer-live-p proof-goals-buffer)]
	  ["Response"
	   (proof-switch-to-buffer proof-response-buffer t)
	   :active (buffer-live-p proof-response-buffer)]
	  ["Trace"
	   (proof-switch-to-buffer proof-trace-buffer)
	   :active (buffer-live-p proof-trace-buffer)
	   :visible proof-shell-trace-output-regexp]
          ["UC file"
	   (proof-switch-to-buffer uc-buffer)
	   :active (buffer-live-p uc-buffer)]
	  ["Shell"
	   (proof-switch-to-buffer proof-shell-buffer)
	   :active (buffer-live-p proof-shell-buffer)]))
  )

(defconst proof-config-menu
  (list "----"
	;; buffer menu might better belong in toolbar menu?
	proof-buffer-menu
	proof-quick-opts-menu)
  "Proof General configuration menu.")
  
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

;; reverting commands adapted from easycrypt-hooks.el

(defvar last-but-one-statenum 0)

;; Function for set or get the information in the span
(defsubst get-span-statenum (span)
  "Return the state number of the SPAN."
  (span-property span 'statenum))

(defsubst set-span-statenum (span val)
  "Set the state number of the SPAN to VAL."
  (span-set-property span 'statenum val))

(defsubst proof-last-locked-span ()
  (with-current-buffer proof-script-buffer
  (span-at (- (proof-unprocessed-begin) 1) 'type)))

(defun last-prompt-info (s)
  "Extract the information from prompt."
  (let ((lastprompt (or s (error "No prompt"))))
    (when (string-match "#\\([0-9]+\\)>" lastprompt)
           (string-to-number (match-string 1 lastprompt))
    )
  )
)

(defun last-prompt-info-safe ()
  "Take from `proof-shell-last-prompt' the last information in the prompt."
  (last-prompt-info proof-shell-last-prompt))

(defun set-state-info ()
  "Set information necessary for backtracking."
  (if proof-shell-last-prompt
     ;; infos = prompt infos of the very last prompt
     ;; sp    = last locked span, which we want to fill with prompt infos
     (let ((sp   (if proof-script-buffer (proof-last-locked-span)))
           (info (or (last-prompt-info-safe) 0 )))

       (unless (or (not sp) (get-span-statenum sp))
         (set-span-statenum sp last-but-one-statenum))
       (setq last-but-one-statenum info)
     )))

(defun find-and-forget (span)
  (let ((span-staten (get-span-statenum span)))
       (list (format "undo %s." (int-to-string span-staten)))))

(defun delete-state-text ()
  "Remove \"state:\" in the configuration window."
  (proof-debug "delete-state-text called")
  (proof-with-current-buffer-if-exists proof-goals-buffer
    (proof-debug (buffer-string))
     (goto-char (point-max))
     (when (re-search-backward "^state:\n" nil t)
        (let* ((inhibit-read-only t)
              )
(proof-debug "found it!!")
              (delete-region (match-beginning 0) (match-end 0))
         )
     )
  )
)

;; command line options

(defun ucdsl-interpreter-load-path-safep (path)
  (and
   (listp path)
   (cl-every #'stringp path)))

(defcustom ucdsl-interpreter-load-path nil
  "Load path for UC DSL interpreter.
This list specifies the load path for UC DSL Interpreter. The elements of
this list are strings."
  :type  '(repeat (string :tag "simple directory (-I)"))
  :safe  'ucdsl-interpreter-load-path-safep
  :group 'ucdsl-interpreter)

;; --------------------------------------------------------------------
(defun ucdsl-interpreter-option-of-load-path-entry (entry)
  (list "-I" (expand-file-name entry)))

;; --------------------------------------------------------------------
(defun ucdsl-interpreter-include-options ()
  (let ((result nil))
    (when ucdsl-interpreter-load-path
      (dolist (entry ucdsl-interpreter-load-path)
        (setq result (append result (ucdsl-interpreter-option-of-load-path-entry entry)))))
    result))

;; --------------------------------------------------------------------
(defun ucdsl-interpreter-build-prog-args ()
  (delete "-interpreter" ucdsl-interpreter-prog-args)
  (push "-interpreter" ucdsl-interpreter-prog-args))

(ucdsl-interpreter-build-prog-args)

;; --------------------------------------------------------------------
(defun ucdsl-interpreter-prog-args ()
  (append ucdsl-interpreter-prog-args (ucdsl-interpreter-include-options)))

;; coloring
;; --------------------------------------------------------------------
(defvar ucdsl-interpreter-keywords '(
  "step"
  "load"
  "functionality"
  "var"
  "real"
  "ideal"
  "send"
  "run"
  "var"
  "assumption"
  "prover"
  "hint"
  "finish"
  "assert"
  "debug"
  "undo"
  "quit"
))

(defvar ucdsl-interpreter-font-lock-keywords
  (list
    (cons (proof-ids-to-regexp ucdsl-interpreter-keywords)    'font-lock-keyword-face)
))

(defun comment-syntax ()
  (modify-syntax-entry ?\* ". 23n")
  (modify-syntax-entry ?\( "()1")
  (modify-syntax-entry ?\) ")(4")
)

(comment-syntax)


;; --------------------------------------------------------------------


;; easy configure adapted from demoisa-easy.el, found in PG-adapting.pdf
(require 'newcomment)
(set (make-local-variable 'comment-quote-nested) nil)

(require 'proof-easy-config)		; easy configure mechanism

(
 proof-easy-config 'ucdsl-interpreter "UC DSL Interpreter"
 proof-prog-name		"ucdsl"
 
 proof-terminal-string		"."
 proof-script-command-end-regexp "[^\\.]\\.\\(\\s \\|\n\\|$\\)"
 
 proof-script-comment-start	"(*"
 proof-script-comment-end	"*)"
 
 proof-goal-command-regexp	"load\\|functionality\\|real\\|ideal"
 proof-save-command-regexp	"finish"

 proof-non-undoables-regexp     "undo\\|debug"
;; proof-undo-n-times-cmd         "undo %s."
;; proof-forget-id-command        "undo %s."
 proof-find-and-forget-fn       'find-and-forget
 
 proof-goal-command		"load %s."
 proof-save-command		"finish."
 
 proof-shell-start-goals-regexp	 "^state:"
 proof-shell-end-goals-regexp	 "^;"

 proof-shell-eager-annotation-start "^\\[warning:0-0\\]\\|^\\[warning:\\|^<dbg>\n\\|^effect:"
 proof-shell-eager-annotation-end   "^;\n\\|^</dbg>\n"

 proof-shell-trace-output-regexp "^<dbg>\n"

 proof-shell-quit-cmd		 "quit."
 proof-assistant-home-page	 "http://yes"
 proof-shell-annotated-prompt-regexp "#[0-9]*>"
 proof-shell-error-regexp	 "^\\[error:"
 
 proof-shell-handle-output-system-specific 'frame-with-uc-file

 proof-shell-handle-delayed-output-hook 'delete-state-text

 proof-shell-handle-error-or-interrupt-hook 
  'highlight-error-hook

 proof-state-change-pre-hook 'set-state-info

 proof-script-font-lock-keywords 'ucdsl-interpreter-font-lock-keywords
 
;; proof-general-debug "non-nil thing"
)

(defpgdefault menu-entries
  '(
    ["Toggle debug mode" (proof-shell-invisible-command "debug")
     ;;:style    toggle
     ;;:selected t;;easycrypt-proof-weak-mode
     :help     "Toggles debug mode."]
))

(defun ucdsl-interpreter-shell-extra-config ()
  (with-current-buffer proof-goals-buffer 
    (rename-buffer "*configuration*")
  )
)

(add-hook 'ucdsl-interpreter-shell-mode-hook 'ucdsl-interpreter-shell-extra-config)

(provide 'ucdsl-interpreter)

;;; ucdsl-interpreter.el ends here
