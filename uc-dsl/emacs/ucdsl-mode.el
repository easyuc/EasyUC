;;; ucdsl-mode.el --- major mode for editing UC DSL code. -*- coding: utf-8; lexical-binding: t; -*-

;; Copyright © 2020

;; This file is not part of GNU Emacs.

;;; License:

;; You can redistribute this program and/or modify it under the terms
;; of the GNU General Public License version 2.

;; This is a major mode for editing UC DSL code. See
;; https://github.com/easyuc/EasyUC

;; simple syntax highlighting

(setq ucdsl-font-lock-keywords
      (let* (
            ;; define several category of keywords
            (x-keywords
             '(
               "Top"
               "adversarial"
               "and"
               "direct"
               "ec_requires"
               "elif"
               "else"
               "end"
               "envport"
               "exists"
               "fail"
               "forall"
               "fun"
               "functionality"
               "if"
               "implements"
               "in"
               "initial"
               "intport"
               "let"
               "match"
               "message"
               "out"
               "party"
               "send"
               "serves"
               "simulates"
               "simulator"
               "state"
               "subfun"
               "then"
               "transition"
               "uc_requires"
               "uses"
               "var"
               "with"
               ))

            ;; generate regex string for each category of keywords
            (x-keywords-regexp (regexp-opt x-keywords 'words)))

        `(
          (,x-keywords-regexp . font-lock-keyword-face)
          ;; note: order above matters, because once colored, that
          ;; part won't change.  in general, put longer words first
          )))

;; set up our syntax table, starting from the one of our parent mode
;; (text-mode)

(defvar ucdsl-mode-syntax-table nil "Syntax table for `ucdsl-mode'.")

(setq ucdsl-mode-syntax-table
      (let ( (synTable (make-syntax-table)))
        (modify-syntax-entry ?. "_" synTable)
        (modify-syntax-entry ?, "_" synTable)
        (modify-syntax-entry ?\; "_" synTable)
        (modify-syntax-entry ?_ "w" synTable)
        (modify-syntax-entry ?' "w" synTable)
        ;; nexted comments (* ... *)
        (modify-syntax-entry ?\( "() 1n" synTable)
        (modify-syntax-entry ?\) ")( 4n" synTable)
        (modify-syntax-entry ?* "_ 23n" synTable)
        synTable))

;; say how to parse error messages from ucdsl command, after
;; the user runs M-x compile

(require 'compile)

(add-to-list 'compilation-error-regexp-alist 'ucdsl)

;; in the following, we say that the second regular expression must
;; match the filename of the ucdsl error/warning message
;;
;; the rest of the message will either be empty or have
;; the form of four numbers
;;    line-start column-start line-end column-end
;;
;; the third regular expression is thus optional, and encloses regular
;; expressions matching the above numbers at positions 4 5 6 7

(add-to-list 'compilation-error-regexp-alist-alist
             '(ucdsl "^\\(error:\\|warning:\\) \\([^ 
]+\\)\\( \\([0-9]+\\) \\([0-9]+\\) \\([0-9]+\\) \\([0-9]+\\)\\)?" 2 (4 . 6) (5 . 7)))

;; hook for mode setting default compilation command, which the user
;; may then edit. -raw-msg is so error/warning messages issued by
;; ucdsl match the format described above

(add-hook 'ucdsl-mode-hook
          (lambda ()
            (set (make-local-variable 'compile-command)
            (concat "ucdsl -raw-msg " buffer-file-name))))

;;;###autoload
(define-derived-mode ucdsl-mode text-mode "UC DSL mode"
  "Major mode for editing UC DSL code"

  ;; code for syntax highlighting
  (setq font-lock-defaults '((ucdsl-font-lock-keywords)))

  ;; install syntax table
  (set-syntax-table ucdsl-mode-syntax-table))

;; add the mode to the `features' list
(provide 'ucdsl-mode)

;;; ucdsl-mode.el ends here
