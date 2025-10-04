;;; minimail.el --- Simple, non-blocking IMAP email client            -*- lexical-binding: t; -*-

;; Copyright (C) 2025  Augusto Stoffel

;; Author: Augusto Stoffel <arstoffel@gmail.com>
;; Keywords: mail

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;; Note on symbol names:
;; - Private symbols start with the "empty prefix" consisting of a
;;   single dash.  This is expanded via the shorthand mechanism to the
;;   usual `minimail--' prefix.
;; - Public symbols are always written in full and have the
;;   `minimail-' prefix.
;; - The `athunk-' prefix is expanded to `minimail--athunk-'.  This
;;   part of the code is independent and could be moved to a separate
;;   package.

;;; Code:

(require 'gnus-art)
(require 'peg)      ;need peg.el from Emacs 30, which is ahead of ELPA
(require 'smtpmail)
(require 'vtable)

(eval-when-compile
  (require 'let-alist)
  (require 'rx)
  (require 'subr-x))

;;; Syntactic sugar for cooperative multitasking
;;
;; A delayed and potentially concurrent computation is represented by
;; what we dub an asynchronous thunk or "athunk".  That is simply a
;; function that takes as argument a callback function or
;; "continuation".  The continuation in turn takes two arguments: an
;; error symbol (which can be nil to indicate success) and a value.
;; The role of the athunk, when called, is to perform some
;; computations and arrange for the continuation to be eventually
;; called.
;;
;; Below are some utilities to write "high-level code" with athunks.
;; This is in a similar vein to the async/await pattern found in some
;; other languages.  The high level code looks linear and doesn't
;; involve callbacks.  There is support for non-local error treatment.
;;
;; References:
;; - https://jyp.github.io/posts/elisp-cps.html
;; - https://nullprogram.com/blog/2019/03/10/
;; - https://lists.gnu.org/archive/html/emacs-devel/2023-03/msg00630.html

(defmacro athunk--let*-1 (cont bindings form)
  "Helper macro for `athunk-let*'."
  (declare (indent 1))
  (cl-flet ((protect (form)
              (let ((esym (gensym)))
                `(condition-case ,esym ,form
                   (t (funcall ,cont (car ,esym) (cdr ,esym)))))))
    (pcase-exhaustive bindings
      ('()
       `(funcall ,cont nil ,(protect form)))
      (`((,var ,exp) . ,rest)
       `(let ((,var ,(protect exp)))
          (athunk--let*-1 ,cont ,rest ,form)))
      (`((,var <- ,athunk) . ,rest)
       (let ((esym (gensym))                ;the error, possibly nil
             (vsym (gensym)))               ;the computed value
         `(funcall ,(protect athunk)
                   (lambda (,esym ,vsym)
                     (if ,esym
                         (funcall ,cont ,esym ,vsym)
                       (let ((,var ,vsym))
                         (athunk--let*-1 ,cont ,rest ,form))))))))))

(defmacro athunk-let* (bindings &rest body)
  "Sequentially resolve athunks then evaluate BODY.
BINDINGS are elements of the form (SYMBOL FORM) or (SYMBOL <- FORM).
The former simply binds FORM's value to SYMBOL.  In the latter, FORM
should evaluate to an athunk, and SYMBOL is bound to it resolved value.

Return an athunk which resolves to the value of the last form in BODY."
  (declare (indent 1) (debug ((&rest (sexp . [&or ("<-" form) (form)])) body)))
  (let ((csym (gensym)))
    `(lambda (,csym)
       (athunk--let*-1 ,csym ,bindings ,(macroexp-progn body)))))

(defmacro athunk-wrap (&rest body)
  "Wrap BODY in an athunk for delayed execution."
  (declare (indent 0))
  `(athunk-let* nil ,@body))

(defun athunk-gather (athunks)
  "Resolve all ATHUNKS and return a vector of results."
  (let* ((n (length athunks))
         (result (make-vector n nil)))
    (lambda (cont)
      (dotimes (i n)
        (funcall (pop athunks)
                 (lambda (err val)
                   (if err
                       (funcall cont err val)
                     (setf (aref result i) val)
                     (when (zerop (cl-decf n))
                       (run-with-timer 0 nil cont nil result)))))))))

(defmacro athunk-let (bindings &rest body)
  "Concurrently resolve athunks then evaluate BODY.
BINDINGS are elements of the form (SYMBOL FORM) or (SYMBOL <- FORM).
The former simply binds FORM's value to SYMBOL.  In the latter, FORM
should evaluate to an athunk, and SYMBOL is bound to it resolved value.

Return an athunk which resolves to the value of the last form in BODY."
  (declare (indent 1))
  (if (length< bindings 2)
      `(athunk-let* ,bindings ,@body)
    (let ((vec (gensym))
          (athunks (mapcar (lambda (binding)
                             (pcase-exhaustive binding
                               (`(,_ <- ,athunk) athunk)
                               (`(,_ ,val) `(athunk-wrap ,val))))
                           bindings))
          (vars (mapcar #'car bindings)))
      `(athunk-let* ((,vec <- (athunk-gather (list ,@athunks))))
         (let ,(seq-map-indexed (lambda (v i) `(,v (aref ,vec ,i))) vars)
           ,@body)))))

(defun athunk-run (athunk)
  "Execute ATHUNK for side-effects.
Any uncatched errors are signaled, but notice this will happen at a
later point in time."
  (prog1 nil
    (funcall athunk (lambda (err val) (when err (signal err val))))))

(defun athunk-debug (athunk &optional prefix)
  "Execute ATHUNK and display result in a message."
  (prog1 nil
    (funcall athunk (lambda (err val)
                      (message "%s:%s:%S" (or prefix "athunk-debug") err val)
                      (when err (signal err val))))))

(defun athunk-sleep (secs &optional value)
  "Return an athunk that waits SECS seconds and then returns VALUE."
  (lambda (cont)
    (run-with-timer secs nil cont nil value)))

(defmacro athunk-condition-case (var form &rest handlers)
  "Like `condition-case', but for asynchronous code.

FORM should evaluate to an athunk.  Return a new athunk that normally
produces the same result as the original; however, if an error is
signaled and one of the HANDLERS apply, then evaluate the handler an
return its result instead.

See `condition-case' for the exact meaning of VAR and HANDLERS."
  (declare (indent 2))
  (let ((csym (gensym))                 ;the continuation
        (esym (gensym))                 ;the error, possibly nil
        (vsym (gensym))                 ;the computed value
        (hsym (gensym)))                ;helper symbol to hold an error
    (unless (assq :success  handlers)
      (push  `(:success ,vsym) handlers))
    `(lambda (,csym)
       (funcall ,form
                (lambda (,esym ,vsym)
                  (condition-case ,hsym
                      (condition-case ,var
                          (when ,esym (signal ,esym ,vsym))
                        ,@handlers)
                    (:success (funcall ,csym nil ,hsym))
                    (t (funcall ,csym (car ,hsym) (cdr ,hsym)))))))))

(defmacro athunk-ignore-errors (&rest body)
  "Like `ignore-errors', but for asynchronous code."
  (declare (indent 0))
  `(athunk-condition-case nil ,(macroexp-progn body) (error nil)))

(defmacro athunk-memoize (place &rest body)
  "Like `with-memoization' for asynchronous code.
BODY should evaluate to an athunk.  When it's resolved, store the result
in PLACE.  If there is already a value stored in PLACE, use it instead."
  (declare (indent 1))
  ;; TODO: error handling
  `(lambda (cont)
     (pcase-exhaustive ,place
       (`(athunk--cached . ,val)
        (funcall cont nil val))
       (`(athunk--pending . ,conts)
        (nconc conts `(,cont)))
       ('nil
        (setf ,place `(athunk--pending ,cont))
        (funcall ,(macroexp-progn body)
                 (lambda (err val)
                   (let ((conts (cdr ,place)))
                     (setf ,place (unless err `(athunk--cached . ,val)))
                     (dolist (k conts)
                       (funcall k err val))))))))) ;FIXME: should ignore errors?

(defmacro athunk-unmemoize (place)
  "Forget the memoized value in PLACE.
This only has an effect if the value has been already computed; if it is
pending the computation is not canceled."
  (gv-letplace (getter setter) place
    `(when (eq 'athunk--cached (car ,getter)) ,(funcall setter nil))))

;;; Customizable options

(defgroup minimail nil
  "Simple, non-blocking IMAP email client."
  :prefix "minimail-"
  :group 'mail)

(defcustom minimail-accounts nil
  "Account configuration for the Minimail client.
This is an alist where keys are names used to refer to each account and
values are a plist with the following information:

:mail-address
  The email address of this account, used to override the global value
  of `user-mail-address'.

:incoming-url
  Information about the IMAP server as a URL. Normally, it suffices to
  enter \"imaps://<server-address>\".  More generally, it can take the form

    imaps://<username>:<password>@<server-address>:<port>

  If username is omitted, use the :mail-address property instead.

  If password is omitted (which is highly recommended), use the
  auth-source mechanism. See Info node `(auth) Top' for details.

:outgoing-url
  Information about the SMTP server as a URL.  Normally, it suffices
  to enter \"smtps://<server-address>\", but you can provide more
  details as in :incoming-url.

:signature
  Overrides the global value of `message-signature'.

:signature-file
  Overrides the global value of `message-signature-file'.

All entries all optional, except for `:incoming-url'."
  :type '(alist
          :key-type (symbol :tag "Account identifier")
          :value-type (plist
                       :tag "Account properties"
                       :value-type string
                       :options (:mail-address
                                 :incoming-url
                                 :outgoing-url
                                 (:signature (choice
                                              (const :tag "None" ignore)
                                              (const :tag "Use `.signature' file" t)
                                              (string :tag "String to insert")
                                              (sexp :tag "Expression to evaluate")))
                                 (:signature-file file)))))

(defcustom minimail-reply-cite-original t
  "Whether to cite the original message when replying."
  :type 'boolean)

(defcustom minimail-connection-idle-timeout 60
  "Time in seconds a network connection can remain open without activity."
  :type 'boolean)

(defcustom minimail-mailbox-mode-columns '((\\Sent flags date recipients subject)
                                           (t flags date from subject))
  "Columns to display in `minimail-mailbox-mode' buffers."
  :type '(repeat alist))

(defcustom minimail-mailbox-mode-sort-by '((t (date . descend)))
  "Sorting criteria for `minimail-mailbox-mode' buffers."
  :type '(repeat alist))

(defface minimail-unread '((t :inherit bold))
  "Face for unread messages.")

;;; Internal variables and helper functions

(defvar -account-state nil
  "Alist mapping accounts to assorted state information about them.")

(defvar-local -local-state nil
  "Place to store assorted buffer-local information.")

(defvar-local -current-account nil)
(defvar-local -current-mailbox nil)

(defvar-local -mode-line-suffix nil)

(defvar -minibuffer-update-hook nil
  "Hook run when minibuffer completion candidates are updated.")

(defvar -debug-buffer nil
  "If non-nil, name of a buffer to display debug information.")

(define-error '-imap-error "error in IMAP response")

(defmacro -get-in (alist key &rest rest)
  (let ((v `(alist-get ,key ,alist nil nil #'equal)))
    (if rest `(-get-in ,v ,(car rest) ,@(cdr rest)) v)))

(defun -get-data (string)
  "Get data stored as a string property in STRING."
  (cl-assert (stringp string))
  (get-text-property 0 'minimail string))

(defvar -log-buffer nil
  "Name of the log buffer, or nil to disable logging.")

(defun -log-message-1 (&rest args)
  "Helper function for `minimail--log-message'.
ARGS is the entire argument list of `minimail--log-message'."
  (with-current-buffer (get-buffer-create -log-buffer)
    (setq-local outline-regexp "")
    (goto-char (point-max))
    (when-let* ((w (get-buffer-window)))
      (set-window-point w (point)))
    (insert #(""  0 1 (invisible t))
            (propertize (format-time-string "[%T] ") 'face 'error)
            (apply #'format args)
            ?\n)))

(defmacro -log-message (string &rest args)
  "Write a message to buffer pointed by `minimail--log-buffer', if non-nil.
The message is formed by calling `format' with STRING and ARGS."
  `(when -log-buffer (-log-message-1 ,string ,@args)))

(defvar minimail-mailbox-history nil
  "History variable for mailbox selection.")

(defun -mailbox-display-name (account mailbox)
  (format "%s:%s" account mailbox))

(defun -key-match-p (condition key)
  "Check whether KEY satisfies CONDITION.
KEY is a string or list of strings."
  (pcase-exhaustive condition
    ('t t)
    ((or (pred symbolp) (pred stringp))
     (if (listp key)
         (seq-some (lambda (s) (string= condition s)) key)
       (string= condition key)))
    (`(regexp ,re)
     (if (listp key)
         (seq-some (lambda (s) (string-match-p re s)) key)
       (string-match-p re key)))
    (`(not ,cond . nil) (not (-key-match-p cond key)))
    (`(or . ,conds) (seq-some (lambda (c) (-key-match-p c key)) conds))
    (`(and . ,conds) (seq-every-p (lambda (c) (-key-match-p c key)) conds))))

(defun -assoc-query (key alist)
  "Look up KEY in ALIST, a list of condition-value pairs.
Return the first matching cons cell."
  (seq-some (lambda (it) (when (-key-match-p (car it) key) it)) alist))

(defun -alist-query (key alist &optional default)
  "Look up KEY in ALIST, a list of condition-value pairs.
Return the first matching value."
  (if-let* ((it (-assoc-query key alist))) (cdr it) default))

(defun -settings-get (keyword account &optional mailbox)
  "Retrieve the most specific configuration value for KEYWORD.

If MAILBOX is non-nil, start looking up
  `minimail-accounts' -> ACCOUNT -> :mailboxes -> MAILBOX -> KEYWORD
If MAILBOX is nil or the above fails, try
  `minimail-accounts' -> ACCOUNT -> KEYWORD
If the above fails and there is a fallback variable associated to
KEYWORD, return the value of that variable."
  (let* ((aconf (cdr (assq account minimail-accounts)))
         (mconf (when mailbox (plist-get :mailboxes aconf)))
         v)
    (cond
     ((setq v (seq-some (pcase-lambda (`(,key . ,value))
                          (and (-key-match-p key mailbox)
                               (plist-member value keyword)))
                        mconf))
      (cadr v))
     ((setq v (plist-member aconf keyword))
      (cadr v))
     ((setq v (assq keyword
                    '((:full-name . user-full-name)
                      (:mail-address . user-mail-address)
                      (:signature . message-signature)
                      (:signature-file . message-signature-file))))
      (symbol-value (cdr v))))))

(defun -settings-alist-get (keyword account mailbox)
  "Retrieve the most specific configuration value for KEYWORD.

First, inspect `minimail-accounts' -> ACCOUNT -> KEYWORD.  If that alist
contains a key matching MAILBOX, return that value.  Otherwise, inspect
variable holding the fallback value for KEYWORD."
  (if-let* ((alist (plist-get (alist-get account minimail-accounts) keyword))
            (val (-assoc-query mailbox alist)))
      (cdr val)
    (let* ((vars '((:mailbox-columns . minimail-mailbox-mode-columns)
                   (:mailbox-sort-by . minimail-mailbox-mode-sort-by)))
           (var (alist-get keyword vars)))
      (-alist-query mailbox (symbol-value var)))))

;;;; vtable hacks

(defvar -vtable-insert-line-hook nil
  "Hook run after inserting each line of a `vtable'.")

(advice-add #'vtable--insert-line :after
            (lambda (&rest _) (run-hooks '-vtable-insert-line-hook))
            '((name . -vtable-insert-line-hook)))


;;; Low-level IMAP communication

;; References:
;; - IMAP4rev1: https://datatracker.ietf.org/doc/html/rfc3501
;; - IMAP4rev2: https://datatracker.ietf.org/doc/html/rfc9051
;; - IMAP URL syntax: https://datatracker.ietf.org/doc/html/rfc5092

(defvar-local -imap-callbacks nil)
(defvar-local -imap-command-queue nil)
(defvar-local -imap-idle-timer nil)
(defvar-local -imap-last-tag nil)
(defvar-local -next-position nil) ;TODO: necessary? can't we just rely on point position?

(defun -imap-connect (account)
  "Return a network stream connected to ACCOUNT."
  (let* ((props (or (alist-get account minimail-accounts)
                    (error "Invalid account: %s" account)))
         (url (url-generic-parse-url (plist-get props :incoming-url)))
         (stream-type (pcase (url-type url)
                        ("imaps" 'tls)
                        ("imap" 'starttls)
                        (other (user-error "\
In `minimail-accounts', incoming-url must have imaps or imap scheme, got %s" other))))
         (user (cond ((url-user url) (url-unhex-string (url-user url)))
                     ((plist-get props :mail-address))))
         (pass (or (url-password url)
                   (auth-source-pick-first-password
                    :user user
                    :host (url-host url)
                    :port (url-portspec url))
                   (error "No password found for account %s" account)))
         (buffer (generate-new-buffer (format " *minimail-%s*" account)))
         (proc (open-network-stream
                (format "minimail-%s" account)
                buffer
                (url-host url)
                (or (url-portspec url)
                    (pcase stream-type
                      ('tls 993)
                      ('starttls 143)))
                :type stream-type
                :coding 'binary
                :nowait t)))
    (add-function :after (process-filter proc) #'-imap-process-filter)
    (set-process-sentinel proc #'-imap-process-sentinel)
    (set-process-query-on-exit-flag proc nil)
    (with-current-buffer buffer
      (set-buffer-multibyte nil)
      (setq -imap-last-tag 0)
      (setq -imap-idle-timer (run-with-timer
                              minimail-connection-idle-timeout nil
                              #'delete-process proc))
      (setq -next-position (point-min)))
    (-imap-enqueue
     proc nil
     (cond
      ;; TODO: use ;AUTH=... notation as in RFC 5092?
      ((string-empty-p user) "AUTHENTICATE ANONYMOUS\r\n")
      (t (format "AUTHENTICATE PLAIN %s"
                 (base64-encode-string (format "\0%s\0%s"
                                               user pass)))))
     (lambda (status message)
       (unless (eq status 'ok)
         (lwarn 'minimail :error "IMAP authentication error (%s):\n%s"
                account message))))
    proc))

(defun -imap-process-sentinel (proc message)
  (-log-message "sentinel: %s %s" proc (process-status proc))
  (pcase (process-status proc)
    ('open
     (with-current-buffer (process-buffer proc)
       (when-let* ((queued (pop -imap-command-queue)))
         (apply #'-imap-send proc queued))))
    ((or 'closed 'failed)
     (with-current-buffer (process-buffer proc)
       (pcase-dolist (`(_ _ . ,cb) -imap-callbacks)
         (funcall cb 'error message)))
     (kill-buffer (process-buffer proc)))))

(defun -imap-process-filter (proc _)
  (timer-set-time -imap-idle-timer
                  (time-add nil minimail-connection-idle-timeout))
  (let ((pos -next-position))
    (when (< pos (point-max))
      (goto-char pos)
      (while (re-search-forward "{\\([0-9]+\\)}\r\n" nil t)
        (let ((pos (+ (point) (string-to-number (match-string 1)))))
          (setq -next-position pos)
          (goto-char (min pos (point-max)))))
      (if (re-search-forward (rx bol
                                 ?A (group (+ digit))
                                 ?\s (group (+ alpha))
                                 ?\s (group (* (not control)))
                                 (? ?\r) ?\n)
                             nil t)
          (pcase-let* ((end (match-beginning 0))
                       (cont (match-end 0))
                       (tag (string-to-number (match-string 1)))
                       (status (intern (downcase (match-string 2))))
                       (message (match-string 3))
                       (`(,mailbox . ,callback) (alist-get tag -imap-callbacks)))
            (setf (alist-get tag -imap-callbacks nil t) nil)
            (-log-message "response: %s %s\n%s"
                          proc
                          (or -current-mailbox "(unselected)")
                          (buffer-string))
            (unwind-protect
                (if (and mailbox (not (equal mailbox -current-mailbox)))
                    (error "Wrong mailbox: %s expected, %s selected"
                           mailbox -current-mailbox)
                  (with-restriction (point-min) end
                    (goto-char (point-min))
                    (funcall callback status message)))
              (delete-region (point-min) cont)
              (setq -next-position (point-min))
              (when-let* ((queued (pop -imap-command-queue)))
                (apply #'-imap-send proc queued))))
        (goto-char (point-max))
        (setq -next-position (pos-bol))))))

(defun -imap-send (proc tag mailbox command)
  "Execute an IMAP COMMAND (provided as a string) in network stream PROC.
TAG is an IMAP tag for the command.
Ensure the given MAILBOX is selected before issuing the command, unless
it is nil."
  (if (or (not mailbox)
          (equal mailbox -current-mailbox))
      (process-send-string proc (format "A%s %s\r\n" tag command))
    ;; Need to select a different mailbox
    (let ((newtag (cl-incf -imap-last-tag))
          (cont (lambda (status message)
                  (if (eq 'ok status)
                      (progn
                        (setq -current-mailbox mailbox)
                        ;; Trick: this will cause the process filter
                        ;; to call `-imap-send' with the original
                        ;; command next.
                        (push (list tag mailbox command) -imap-command-queue))
                    (let ((callback (alist-get tag -imap-callbacks)))
                      (setf (alist-get tag -imap-callbacks nil t) nil)
                      (funcall callback status message))))))
      (push `(,newtag nil . ,cont) -imap-callbacks)
      (process-send-string proc (format "A%s SELECT %s\r\n"
                                        newtag (-imap-quote mailbox))))))

(defun -imap-enqueue (proc mailbox command callback)
  (with-current-buffer (process-buffer proc)
    (let ((tag (cl-incf -imap-last-tag)))
      (if (or -imap-callbacks
              ;; Sending to process in `connect' state blocks Emacs,
              ;; so delay it
              (not (eq 'open (process-status proc))))
          (cl-callf nconc -imap-command-queue `((,tag ,mailbox ,command)))
        (-imap-send proc tag mailbox command))
      (push `(,tag ,mailbox . ,callback) -imap-callbacks))))

;;; IMAP parsing

;; References:
;; - Formal syntax: https://datatracker.ietf.org/doc/html/rfc3501#section-9

(defalias '-imap-quote #'json-serialize ;good enough approximation
  "Make a quoted string as per IMAP spec.")

(defconst -imap-months
  ["Jan" "Feb" "Mar" "Apr" "May" "Jun" "Jul" "Aug" "Sep" "Oct" "Nov" "Dec"])

(defun -imap-parse-error (pegs)
  "Report an error parsing IMAP server response."
  (-log-message "parsing failed at position %s:%s: %S"
                (line-number-at-pos)
                (- (point) (pos-bol) -1)
                pegs)
  (error "Error parsing IMAP response"))

(define-peg-ruleset -imap-peg-rules
  (sp        () (char ?\s))
  (dquote   ()  (char ?\"))
  (crlf      () "\r\n")
  (anil      () "NIL" `(-- nil))
  (untagged  () (bol) "* ")
  (number    () (substring (+ [0-9])) `(s -- (string-to-number s)))
  (achar     () (and (not [cntrl "(){] %*\"\\"]) (any))) ;characters allowed in an atom
  (atom      () (substring (+ achar)))  ;non-quoted identifier a.k.a. atom
  (qchar     () (or (and (char ?\\) [?\" ?\\]) ;character of a quoted string
                    (and (not dquote) (any))))
  (qstring   () dquote (substring (* qchar)) dquote ;quoted string
                `(s -- (replace-regexp-in-string (rx ?\\ (group nonl)) "\\1" s)))
  (literal   ()
             (char ?{)
             (guard (re-search-forward (rx point (group (+ digit)) "}\r\n") nil t))
             (region ;little hack: assume match data didn't change between the guards
              (guard (progn (forward-char (string-to-number (match-string 1)))
                            t))))
  (lstring   () literal      ;a "safe" string extracted from a literal
                `(start end -- (replace-regexp-in-string
                                (rx control) ""
                                (buffer-substring-no-properties start end))))
  (string    () (or qstring lstring))
  (qpstring  ()                         ;quoted string, QP-encoded
             string
             `(s -- (mail-decode-encoded-word-string s)))
  (astring   () (or atom string))
  (nstring   () (or anil string))
  (nqpstring () (or anil qpstring))
  (timezone  ()
             (or (and (char ?+) `(-- +1))
                 (and (char ?-) `(-- -1)))
             number
             `(sign n -- (let* ((h (/ n 100))
                                (m (mod n 100)))
                           (* sign (+ (* 3600 h) (* 60 m))))))
  (month     ()
             (substring [A-Z] [a-z] [a-z])
             `(s -- (1+ (seq-position -imap-months s))))
  (imapdate  ()
             (char ?\") (opt sp) number (char ?-) month (char ?-) number
             sp number (char ?:) number (char ?:) number
             sp timezone (char ?\")
             `(day month year hour min sec tz
                   -- `(,sec ,min ,hour ,day ,month ,year nil -1 ,tz)))
  (flag      ()
             (substring (opt "\\") (+ achar)))
  (to-eol    ()                         ;consume input until eol
             (* (and (not [cntrl]) (any))) crlf)
  (to-rparen ()                    ;consume input until closing parens
             (* (or (and "(" to-rparen)
                    (and dquote (* qchar) dquote)
                    (and (not [cntrl "()\""]) (any))))
             ")")
  (balanced  () "(" to-rparen))

(defun -parse-capability ()
  (with-peg-rules
      (-imap-peg-rules
       (iatom (substring (+ (and (not (char ?=)) achar)))
              `(s -- (intern (downcase s))))
       (paramcap iatom (char ?=) (or number iatom)
                 `(k v -- (cons k v)))
       (caps (list (* sp (or paramcap iatom)))))
    (car-safe
     (peg-run (peg untagged "CAPABILITY" caps crlf)
              #'-imap-parse-error))))

(defun -parse-list ()
  (with-peg-rules
      (-imap-peg-rules
       (flags (list (* (opt sp) flag)))
       (item untagged "LIST (" flags ") "
             (or astring anil)
             sp astring
             `(f d n -- `(,n (delimiter . ,d) (attributes . ,f))))
       (status untagged "STATUS "
               (list astring " ("
                     (* (opt sp)
                        (or (and "MESSAGES " number `(n -- `(messages . ,n)))
                            (and "RECENT " number `(n -- `(recent . ,n)))
                            (and "UIDNEXT " number `(n -- `(uid-next . ,n)))
                            (and "UIDVALIDITY " number `(n -- `(uid-validity . ,n)))
                            (and "UNSEEN " number `(n -- `(unseen . ,n)))))
                     ")"))
       (response (list (* (or item status) crlf))))
    (let* ((lines (car (peg-run (peg response))))
           (grouped (seq-group-by #'car lines)))
      (mapcar (pcase-lambda (`(,k . ,v)) `(,k . ,(mapcan #'cdr v)))
              grouped))))

(defun -parse-select ()
  (with-peg-rules
      (-imap-peg-rules
       (item (or
              (and "FLAGS (" (list (* (opt sp) flag)) ")" crlf
                   `(v -- `(flags . ,v)))
              (and number " EXISTS" crlf
                   `(n -- `(exists . ,n)))
              (and number " RECENT" crlf
                   `(n -- `(recent . ,n)))
              (and "OK [UNSEEN " number "]" to-eol
                   `(n -- `(unseen . ,n)))
              (and "OK [UIDNEXT " number "]" to-eol
                   `(n -- `(uid-next . ,n)))
              (and "OK [UIDVALIDITY " number "]" to-eol
                   `(n -- `(uid-validity . ,n)))
              (and "OK" to-eol))))
    (car-safe
     (peg-run (peg (list (* untagged item)))))))

(defun -parse-fetch ()
  (with-peg-rules
      (-imap-peg-rules
       (address "("
                (list (and nqpstring `(s -- `(name . ,s)))
                      sp (and nstring `(_ --)) ;discard useless addr-adl field
                      sp (and nstring `(s -- `(mailbox . ,s)))
                      sp (and nstring `(s -- `(host . ,s))))
                ")")
       (addresses (or anil
                      (and "(" (list (* address)) ")")))
       (envelope "ENVELOPE ("
                 (list nstring `(s -- `(date . ,(when s (parse-time-string s))))
                       sp nqpstring `(s -- `(subject . ,s))
                       sp addresses `(v -- `(from . ,v))
                       sp addresses `(v -- `(sender . ,v))
                       sp addresses `(v -- `(reply-to . ,v))
                       sp addresses `(v -- `(to . ,v))
                       sp addresses `(v -- `(cc . ,v))
                       sp addresses `(v -- `(bcc . ,v))
                       sp nstring `(v -- `(in-reply-to . ,v))
                       sp nstring `(v -- `(message-id . ,v)))
                 ")"
                 `(s -- `(envelope . ,s)))
       (body-param (or anil
                       (list "("
                             (+ (opt sp) qstring sp qstring
                                `(k v -- (cons k v)))
                             ")")))
       (body-single "("
                    (list qstring `(s -- `(media-type . ,s))
                          sp qstring `(s -- `(media-subtype . ,s))
                          sp body-param `(s -- `(media-params . ,s))
                          sp nstring `(s -- `(id . ,s))
                          sp nstring `(s -- `(description . ,s))
                          sp qstring `(s -- `(encoding . ,s))
                          sp number `(s -- `(octets . ,s))
                          (opt sp envelope sp (or body-multi body-single))
                          (opt sp number `(s -- `(lines . ,s)))
                          (* sp astring)) ;body extensions, ignored here
                    ")")
       (body-multi "("
                   (list (list (+ (or body-multi body-single)))
                         `(v -- `(parts . ,v))
                         sp qstring
                         `(s -- '(media-type . "MULTIPART") `(media-subtype . ,s)))
                   ")")
       ;; (body "BODY " (or body-single body-multi)
       ;;       `(s -- `(body . ,s)))
       (body "BODY " ;; (funcall (lambda () (forward-sexp) t))
             balanced
             )
       (content "BODY[] " literal `(start end -- `(content ,start . ,end)))
       (flags "FLAGS (" (list (* (opt sp) flag)) ")"
              `(v -- `(flags . ,v)))
       (internal-date "INTERNALDATE " imapdate
                     `(v -- `(internal-date . ,v)))
       (size "RFC822.SIZE " number `(n -- `(rfc822-size . ,n)))
       (uid "UID " number `(n -- `(uid . ,n)))
       (item untagged number `(n -- `(id . ,n))
             " FETCH ("
             (* (opt sp) (or uid flags size envelope body content internal-date))
             ")" crlf))
    (car-safe
     (peg-run (peg (list (* (list item))))))))

(defun -parse-search ()
  (with-peg-rules
      (-imap-peg-rules
       (search "SEARCH" (list (* sp number)))
       (esearch "ESEARCH"
                (list
                 (* sp (or (and "(TAG " qstring `(s -- `(tag . ,s)) ")")
                           (and "UID" `(-- '(uid . t)))
                           (and "ALL " atom `(s -- `(set . ,s)))
                           (and "MIN " number `(n -- `(min . ,n)))
                           (and "MAX " number `(n -- `(max . ,n)))
                           (and "COUNT " number `(n -- `(count . ,n))))))))
    (car-safe
     (peg-run (peg untagged (or esearch search) crlf)))))

;;; Async IMAP requests

(defun -amake-request (account mailbox command)
  "Issue COMMAND to the ACCOUNT's IMAP server.
If MAILBOX is non-nil, ensure it is selected beforehand.

Returns an athunk which resolves to a temporary buffer containing the
server response.  The temporary buffer is cleaned up automatically after
being used."
  (lambda (cont)
    (let ((proc (-get-in -account-state account 'process)))
      (unless (process-live-p proc)
        (setq proc (-imap-connect account))
        (setf (-get-in -account-state account 'process) proc))
      (-imap-enqueue
       proc mailbox command
       (lambda (status message)
         (if (not (eq 'ok status))
             (funcall cont '-imap-error (list status message))
           (let* ((buffer (current-buffer))
                  (tmpbuf (generate-new-buffer " *minimail-temp*"))
                  (continue (lambda ()
                              (unwind-protect
                                  (funcall cont nil tmpbuf)
                                (kill-buffer tmpbuf)))))
             (with-current-buffer tmpbuf
               (set-buffer-multibyte nil)
               (insert-buffer-substring buffer)
               (goto-char (point-min)))
             (run-with-idle-timer 0 nil continue))))))))

(defun -aget-capability (account)
  (athunk-memoize (-get-in -account-state account 'capability)
    (athunk-let*
        ((buffer <- (-amake-request account nil "CAPABILITY")))
      (with-current-buffer buffer
        (-parse-capability)))))

(defun -aget-mailbox-listing (account &optional refresh)
  (when refresh
    (athunk-unmemoize (-get-in -account-state account 'mailboxes)))
  (athunk-memoize (-get-in -account-state account 'mailboxes)
    (athunk-let*
        ((props (alist-get account minimail-accounts))
         (url (url-generic-parse-url (plist-get props :incoming-url)))
         (path (string-remove-prefix "/" (car (url-path-and-query url))))
         (caps <- (-aget-capability account))
         (cmd (format "LIST %s *%s"
                      (-imap-quote path)
                      (if (memq 'list-status caps)
                          " RETURN (SPECIAL-USE STATUS (MESSAGES UIDNEXT UNSEEN))" ;FIXME check special-use cap
                        "")))
         (buffer <- (-amake-request account nil cmd)))
      (with-current-buffer buffer
        (-parse-list)))))

(defun -aget-mailbox-attributes (account mailbox)
  (athunk-let*
      ((mailboxes <- (-aget-mailbox-listing account)))
    (-get-in mailboxes mailbox 'attributes)))

(defun -aget-mailbox-status (account mailbox)
  (athunk-let*
      ((cmd (format "EXAMINE %s" (-imap-quote mailbox)))
       (buffer <- (-amake-request account nil cmd)))
    (with-current-buffer buffer
      (-parse-select))))

(defun -afetch-id (account mailbox uid)
  "Fetch a message ID given its UID, MAILBOX and ACCOUNT."
  (athunk-let*
      ((buffer <- (-amake-request account mailbox
                                  (format "%sFETCH %s (UID)"
                                          (if uid "UID " "")
                                          (or uid "*")))))
    ;;FIXME: uid=nil was supposed to retrieve the highest id, but
    ;;servers seem to implement some kind of caching that make it not
    ;;work.
    (with-current-buffer buffer
      (alist-get 'id (car (-parse-fetch))))))

(defun -afetch-mailbox (account mailbox num &optional end)
  (athunk-let*
      ((status <- (-aget-mailbox-status account mailbox))
       (endid (alist-get 'exists status))
       (last (if end (1- endid) endid)) ;FIXME?
       (first (max 1 (- last num -1)))
       (cmd (format "FETCH %s:%s (UID FLAGS RFC822.SIZE ENVELOPE)"
                    first last))
       (buffer <- (-amake-request account mailbox cmd)))
    (with-current-buffer buffer
      (-parse-fetch))))

(defun -afetch-message (account mailbox uid)
  (athunk-let*
      ((cmd (format "UID FETCH %s (BODY[])" uid))
       (buffer <- (-amake-request account mailbox cmd)))
    (with-current-buffer buffer
      (pcase-let* ((data (car (-parse-fetch)))
                   (`(,start . ,end) (alist-get 'content data)))
        (narrow-to-region start end)
        (goto-char (point-min))
        ;; Somehow needed to make quoted-printable decoding work...
        (replace-string-in-region "\r\n" "\n")
        buffer))))

(defun -format-search-1 (item)
  (pcase-exhaustive item
    (`(or ,first . nil)
     (-format-search-1 first))
    (`(or ,first . ,rest)
     (concat "OR " (-format-search-1 first) " " (-format-search-1 `(or . ,rest))))
    (`(not . ,v)
     (concat "NOT " (-format-search-1 v)))
    ((or 'all 'answered 'deleted 'flagged 'seen 'draft)
     (upcase (symbol-name item)))
    (`(,(and k (or 'keyword 'larger 'smaller)) . ,v) ;atom or number argument
     (format "%s %s" (upcase (symbol-name k)) v))
    (`(,(and k (or 'bcc 'body 'cc 'from 'subject 'text 'to)) . ,v) ;string argument
     (format "%s %S" (upcase (symbol-name k)) v))
    (`(,(and k (or 'before 'on 'since 'sentbefore 'senton 'sentsince)) . ,v) ;date argument
     (pcase-let ((`(_ _ _ ,day ,month ,year) (parse-time-string v)))
       (format "%s %s-%s-%s"
               (upcase (symbol-name k))
               day (aref -imap-months (1- month)) year)))
    (`(header ,k . ,v)
     (format "HEADER %S %S" k v))
    ((pred proper-list-p)
     (concat "(" (-format-search item) ")"))))

(defun -format-search (query)
  (mapconcat #'-format-search-1 (or query '(all)) " "))

(defun -afetch-search (account mailbox query)
  (athunk-let*
      ((sbuf <- (-amake-request account mailbox
                                (concat "UID SEARCH CHARSET UTF-8 " (-format-search query))))
       (uids (with-current-buffer sbuf (-parse-search)))
       (fbuf <- (-amake-request account mailbox
                                (format "UID FETCH %s (UID FLAGS RFC822.SIZE ENVELOPE)"
                                        (mapconcat #'number-to-string uids ",")))))
    (with-current-buffer fbuf
      (-parse-fetch))))

(defun -format-sequence-set (messages)
  (cond
   ((stringp messages) messages)
   ((numberp messages) (number-to-string messages))
   (t (mapconcat #'number-to-string messages ","))))

(defun -amove-messages (account mailbox destination uids)
  (athunk-let*
      ((caps <- (-aget-capability account))
       (cmd (if (memq 'move caps)
                (format "UID MOVE %s %s"
                        (-format-sequence-set uids)
                        (-imap-quote destination))
              (error "Account %s doesn't support moving messages" account)))
       (_ <- (-amake-request account mailbox cmd)))
    t))

;;; Commands

(defmacro -with-associated-buffer (buffer &rest body)
  (declare (indent 1))
  (let ((bsym (gensym)))
    `(let ((,bsym (if (derived-mode-p ',(intern (format "minimail-%s-mode" buffer)))
                      (current-buffer)
                    (-get-in -local-state ',(intern (format "%s-buffer" buffer))))))
       (unless (buffer-live-p ,bsym)
         (user-error "No %s buffer" ',buffer))
       (with-current-buffer ,bsym ,@body))))

(defun -mailbox-buffer (&optional noerror)
  (let ((buffer (if (derived-mode-p 'minimail-mailbox-mode)
                    (current-buffer)
                  (alist-get 'mailbox-buffer -local-state))))
    (prog1 buffer
      (unless (or noerror (buffer-live-p buffer))
        (user-error "No mailbox buffer")))))

(defun -mailbox-annotate (cand)
  "Return an annotation for `devdocs--read-entry' candidate CAND."
  (let-alist (car (-get-data cand))
    (when .messages
      (if (cl-plusp .unseen)
          (format #("  %s messages, %s unseen" 1 2 (display (space :align-to 40)))
                  .messages .unseen)
        (format #("  %s messages" 1 2 (display (space :align-to 40)))
                  .messages)))))

(defun -read-mailbox (prompt &optional accounts)
  "Read the name of a mailbox from one of the ACCOUNTS using PROMPT.
If ACCOUNTS is nil, use all configured accounts.
Return a cons cell consisting of the account symbol and mailbox name."
  (let* (cands
         ov
         (accounts (or (ensure-list accounts)
                       (mapcar #'car minimail-accounts)
                       (user-error "No accounts configured")))
         (metadata '(metadata
                     (category . minimail-mailbox)
                     (annotation-function . -mailbox-annotate)))
         (coll (lambda (string predicate action)
                 (if (eq action 'metadata)
                     metadata
                   (complete-with-action action cands string predicate)))))
    (minibuffer-with-setup-hook
        (lambda()
          (setq ov (make-overlay (- (minibuffer-prompt-end) 2)
                                 (- (minibuffer-prompt-end) 1)))
          (overlay-put ov 'display " (loading):")
          (dolist (acct accounts)
            (athunk-run
             (athunk-let*
                 ((mkcand (pcase-lambda (`(,mbx . ,props))
                            (unless (memq '\\Noselect (alist-get 'attributes props))
                              (propertize (-mailbox-display-name acct mbx)
                                          'minimail `(,props ,acct . ,mbx)))))
                  (mailboxes <- (athunk-condition-case err
                                    (-aget-mailbox-listing acct)
                                  (t (overlay-put ov 'display " (error):")
                                     (message "Error loading mailboxes for account %s: %S"
                                              acct err)
                                     nil))))
               (when ov ;non-nil means we're still reading from minibuffer
                 (setq cands (nconc (delq nil (mapcar mkcand mailboxes)) cands))
                 (with-current-buffer (overlay-buffer ov)
                   (run-hooks '-minibuffer-update-hook))
                 (cl-remf accounts acct)
                 (unless accounts (delete-overlay ov)))))))
      (let ((cand (unwind-protect
                      (completing-read prompt coll nil t nil 'minimail-mailbox-history)
                    (setq ov nil))))
        (cdr (-get-data (or (car (member cand cands))
                            (user-error "Not a mailbox!"))))))))

(defun -read-mailbox-maybe (prompt)
  "Read a mailbox using PROMPT, unless current buffer is related to a mailbox."
  (if -current-mailbox
      (cons -current-account -current-mailbox)
    (-read-mailbox prompt -current-account)))

(defun -selected-messages ()
  (cond
   ((derived-mode-p 'minimail-message-mode)
    (error "Not implemented"))
   ((derived-mode-p 'minimail-mailbox-mode)
    (list -current-account
          -current-mailbox
          (list (alist-get 'uid (or (vtable-current-object)
                                    (user-error "No selected message"))))))))

;;;###autoload
(defun minimail-find-mailbox (account mailbox)
  "List messages in a mailbox."
  (interactive (let ((v (-read-mailbox "Find mailbox: ")))
                 `(,(car v) ,(cdr v))))
  (pop-to-buffer
   (let* ((name (-mailbox-display-name account mailbox))
          (buffer (get-buffer name)))
     (unless buffer
       (setq buffer (get-buffer-create name))
       (with-current-buffer buffer
         (minimail-mailbox-mode)
         (setq -current-account account)
         (setq -current-mailbox mailbox)
         (-mailbox-refresh)))
     buffer)))

;;;###autoload
(defun minimail-search (account mailbox query)
  "Perform a search in ACCOUNT's MAILBOX."
  (interactive (pcase-let*
                   ((`(,acct . ,mbx) (-read-mailbox-maybe "Search in mailbox: "))
                    (text (read-from-minibuffer "Search text: ")))
                 `(,acct ,mbx ((text . ,text)))))
  (pop-to-buffer
   (let* ((name (format "*search in %s*"
                        (-mailbox-display-name account mailbox)))
          (buffer (get-buffer-create name)))
     (with-current-buffer buffer
       (minimail-mailbox-mode)
       (setq -current-account account)
       (setq -current-mailbox mailbox)
       (setq -local-state `((search . ,query)))
       (-mailbox-refresh))
     buffer)))

(defun -amove-messages-and-redisplay (account mailbox destination uids)
  (athunk-let*
      ((prog (make-progress-reporter
              (format-message "Moving messages to `%s'..."
                              (-mailbox-display-name account destination))))
       (_ <- (-amove-messages account mailbox destination uids)))
    (progress-reporter-done prog)
    (when-let*
        ((mbxbuf (seq-some (lambda (buf)
                             (with-current-buffer buf
                               (and (derived-mode-p 'minimail-mailbox-mode)
                                    (eq account -current-account)
                                    (equal mailbox -current-mailbox)
                                    buf)))
                           (buffer-list))))
      (with-current-buffer mbxbuf
        (let* ((table (vtable-current-table))
               (objs (vtable-objects table)))
          (dolist (obj objs)
            (when (memq (alist-get 'uid obj) uids)
              (vtable-remove-object table obj))))))))

(defun minimail-move-to-mailbox (&optional destination)
  (interactive nil minimail-mailbox-mode minimail-message-mode)
  (pcase-let* ((`(,acct ,mbx ,uids) (-selected-messages))
               (prompt (if (length= uids 1)
                           "Move message to: "
                         (format "Move %s messages to: " (length uids))))
               (dest (or destination
                         (cdr (-read-mailbox prompt (list acct))))))
    (athunk-run (-amove-messages-and-redisplay acct mbx dest uids))))

(defun -find-mailbox-by-attribute (attr mailboxes)
  (seq-some (pcase-lambda (`(,mbx . ,items))
              (when (memq attr (alist-get 'attributes items)) mbx))
            mailboxes))

(defun minimail-move-to-archive ()
  (interactive nil minimail-mailbox-mode minimail-message-mode)
  (pcase-let* ((`(,acct ,mbx ,uids) (-selected-messages)))
    (athunk-run
     (athunk-let*
         ((mailboxes <- (-aget-mailbox-listing acct))
          (_ <- (let ((dest (or (plist-get (alist-get acct minimail-accounts)
                                        :archive-mailbox)
                             (-find-mailbox-by-attribute '\\Archive mailboxes)
                             (-find-mailbox-by-attribute '\\All mailboxes)
                             (user-error "Archive mailbox not found"))))
               (-amove-messages-and-redisplay acct mbx dest uids))))))))

(defun minimail-move-to-trash ()
  (interactive nil minimail-mailbox-mode minimail-message-mode)
  (pcase-let* ((`(,acct ,mbx ,uids) (-selected-messages)))
    (athunk-run
     (athunk-let*
         ((mailboxes <- (-aget-mailbox-listing acct))
          (_ <- (let ((dest (or (plist-get (alist-get acct minimail-accounts)
                                        :trash-mailbox)
                             (-find-mailbox-by-attribute '\\Trash mailboxes)
                             (user-error "Trash mailbox not found"))))
               (-amove-messages-and-redisplay acct mbx dest uids))))))))

(defun minimail-move-to-junk ()
  (interactive nil minimail-mailbox-mode minimail-message-mode)
  (pcase-let* ((`(,acct ,mbx ,uids) (-selected-messages)))
    (athunk-run
     (athunk-let*
         ((mailboxes <- (-aget-mailbox-listing acct))
          (_ <- (let ((dest (or (plist-get (alist-get acct minimail-accounts)
                                        :junk-mailbox)
                             (-find-mailbox-by-attribute '\\Junk mailboxes)
                             (user-error "Junk mailbox not found"))))
               (-amove-messages-and-redisplay acct mbx dest uids))))))))

;;; Mailbox buffer

(defvar-local -thread-tree nil
  "The thread tree for the current buffer, as in RFC 5256.")

(defvar-keymap minimail-mailbox-mode-map
  "RET" #'minimail-show-message
  "n" #'minimail-next-message
  "p" #'minimail-previous-message
  "r" #'minimail-reply
  "R" #'minimail-reply-all
  "f" #'minimail-forward
  "s" #'minimail-search
  "g" #'revert-buffer
  "q" #'minimail-quit-windows
  "T" #'minimail-sort-by-thread
  "SPC" #'minimail-message-scroll-up
  "S-SPC" #'minimail-message-scroll-down
  "DEL" #'minimail-message-scroll-down)

(define-derived-mode minimail-mailbox-mode special-mode
  '("Mailbox" -mode-line-suffix)
  "Major mode for mailbox listings."
  :interactive nil
  (add-hook '-vtable-insert-line-hook #'-apply-mailbox-line-face nil t)
  (setq-local
   revert-buffer-function #'-mailbox-refresh
   truncate-lines t))

(defun -base-subject (string)
  "Simplify message subject STRING for sorting and threading purposes.
Cf. RFC 5256, §2.1."
  (replace-regexp-in-string message-subject-re-regexp "" (downcase string)))

(defun -format-names (addresses &rest _)
  (propertize
   (mapconcat
    (lambda (addr)
      (let-alist addr
        (or .name .mailbox "(unknown)")))
    addresses
    ", ")
   'help-echo
   (lambda (&rest _)
     (mapconcat
      (lambda (addr)
        (let-alist addr
          (mail-header-make-address .name (concat .mailbox "@" .host))))
      addresses
      "\n"))))

(defun -format-date (date &rest _)
  (when (stringp date)
    (setq date (-get-data date)))
  (let* ((current-time-list nil)
         (timestamp (encode-time date))
         (today (let* ((v (decode-time)))
                  (setf (decoded-time-hour v) 0)
                  (setf (decoded-time-minute v) 0)
                  (setf (decoded-time-second v) 0)
                  v))
         ;; Message age in seconds since start of this day
         (age (- (encode-time today) timestamp))
         (fmt (cond
               ((<= age (- (* 24 60 60))) "%Y %b %d")
               ((<= age 0) "%R")
               ((<= age (* 6 24 60 60)) "%a %R")
               ((<= (encode-time `(0 0 0 1 1 ,(decoded-time-year today)))
                    timestamp)
                "%b %d")
               (t "%Y %b %d"))))
    (propertize
     (format-time-string fmt timestamp)
     'help-echo (lambda (&rest _)
                  (format-time-string "%a, %d %b %Y %T %z"
                                      timestamp
                                      (decoded-time-zone date))))))

(defvar minimail-flag-icons
  '((((not \\Seen) . #("\1" 0 1 (invisible t))) ;invisible column to sort unread first
     (t            . #("\2" 0 1 (invisible t))))
    ((\\Flagged  . "★")
     ($Important . #("★" 0 1 (face shadow))))
    ((\\Answered . "↩")
     ($Forwarded . "→")
     ($Junk      . #("⚠" 0 1 (face shadow)))
     ($Phishing  . #("⚠" 0 1 (face error))))))

(defvar minimail-flag-faces
  '(((not \\Seen) . minimail-unread)))

(defun -apply-mailbox-line-face ()
  (save-excursion
    (when-let* ((end (prog1 (point) (goto-char (pos-bol 0))))
                (flags (assq 'flags (vtable-current-object)))
                (face (-alist-query (cdr flags) minimail-flag-faces)))
      (add-face-text-property (point) end face))))

(defun -message-timestamp (msg)
  "The message's envelope date as a Unix timestamp."
  (let-alist msg
    (let ((current-time-list nil))
      (encode-time (or .envelope.date
                       .internal-date
                       '(0 0 0 1 1 1970 nil nil 0))))))

(defvar minimail-mailbox-mode-column-alist
  ;; NOTE: We must slightly abuse the vtable API in several of our
  ;; column definitions.  The :getter attribute returns a string used
  ;; as sort key while :formatter fetches from it the actual display
  ;; string, embedded as a string property.
  `((id
     :name "#"
     :getter ,(lambda (msg _) (alist-get 'id msg)))
    (flags
     :name ""
     :getter ,(lambda (msg _)
                (let-alist msg
                  (propertize
                   (mapconcat (lambda (column)
                                (-alist-query .flags column " "))
                              minimail-flag-icons)
                   'help-echo (lambda (&rest _)
                                (if .flags
                                    (string-join (cons "Message flags:" .flags) " ")
                                  "No message flags"))))))
    (from
     :name "From"
     :max-width 30
     :getter ,(lambda (msg _)
                (let-alist msg
                  (-format-names .envelope.from))))
    (to
     :name "To"
     :max-width 30
     :getter ,(lambda (msg _)
                (let-alist msg
                  (-format-names .envelope.to))))
    (recipients
     :name "Recipients"
     :max-width 30
     :getter ,(lambda (msg _)
                (let-alist msg
                  (-format-names (append .envelope.to
                                         .envelope.cc
                                         .envelope.bcc)))))
    (subject
     :name "Subject"
     :max-width 60
     :getter ,(lambda (msg tbl)
                (let-alist msg
                  (propertize (let ((s (-base-subject (or .envelope.subject ""))))
                                (if (string-empty-p s) "\0" s))
                              'minimail `((table . ,tbl) ,@msg))))
     :formatter ,(lambda (s)
                   (let-alist (-get-data s)
                     (concat (when (not (vtable-sort-by .table)) ;means sorting by thread
                               (-thread-subject-prefix .uid))
                             (or .envelope.subject "")))))
    (date
     :name "Date"
     :width 12
     :getter ,(lambda (msg _)
                ;; The envelope date as Unix timestamp, formatted as a
                ;; hex string.  This ensures the correct sorting.
                (propertize (format "%09x" (-message-timestamp msg))
                            'minimail (let-alist msg .envelope.date)))
     :formatter -format-date)))

(defun -mailbox-refresh (&rest _)
  (unless (derived-mode-p #'minimail-mailbox-mode)
    (user-error "This should be called only from a mailbox buffer."))
  (let ((buffer (current-buffer))
        (account -current-account)
        (mailbox -current-mailbox)
        (search (alist-get 'search -local-state)))
    (setq -mode-line-suffix ":Loading")
    (athunk-run
     (athunk-let*
         ((attrs <- (-aget-mailbox-attributes account mailbox))
          (messages <- (athunk-condition-case err
                           (if search
                               (-afetch-search account mailbox search)
                             (-afetch-mailbox account mailbox 100))
                         (t (with-current-buffer buffer
                              (setq -mode-line-suffix ":Error"))
                            (signal (car err) (cdr err))))))
       (with-current-buffer buffer
         (setq -mode-line-suffix nil)
         (setq -thread-tree (-thread-by-subject messages))
         (if-let* ((vtable (vtable-current-table)))
             (progn
               (setf (vtable-objects vtable) messages)
               (vtable-revert-command))
           (erase-buffer)
           (let* ((inhibit-read-only t)
                  (key (cons mailbox attrs))
                  (colnames (-settings-alist-get :mailbox-columns account key))
                  (sortnames (-settings-alist-get :mailbox-sort-by account key)))
             (make-vtable
              :objects messages
              :keymap minimail-mailbox-mode-map
              :columns (mapcar (lambda (v)
                                 (alist-get v minimail-mailbox-mode-column-alist))
                               colnames)
              :sort-by (mapcan (pcase-lambda (`(,col . ,dir))
                                 (when-let ((i (seq-position colnames col)))
                                   `((,i . ,dir))))
                               sortnames)))))))))

(defun minimail-show-message ()
  (interactive nil minimail-mailbox-mode)
  (let ((account -current-account)
        (mailbox -current-mailbox)
        (message (vtable-current-object))
        (mbxbuf (current-buffer))
        (msgbuf (if-let* ((buffer (alist-get 'message-buffer -local-state))
                          (_ (buffer-live-p buffer)))
                    buffer
                  (setf (alist-get 'message-buffer -local-state)
                        (generate-new-buffer
                         (-message-buffer-name -current-account
                                               -current-mailbox
                                               ""))))))
    (cl-pushnew '\\Seen (alist-get 'flags message))
    (vtable-update-object (vtable-current-table) message)
    (setq-local overlay-arrow-position (copy-marker (pos-bol)))
    (with-current-buffer msgbuf
      (-display-message account mailbox (alist-get 'uid message))
      (setf (alist-get 'mailbox-buffer -local-state) mbxbuf))))

(defun minimail-next-message (count)
  (interactive "p" minimail-mailbox-mode minimail-message-mode)
  (-with-associated-buffer mailbox
    (if (not overlay-arrow-position)
        (goto-char (point-min))
      (goto-char overlay-arrow-position)
      (goto-char (pos-bol (1+ count))))
    (when-let* ((window (get-buffer-window)))
      (set-window-point window (point)))
    (minimail-show-message)))

(defun minimail-previous-message (count)
  (interactive "p" minimail-mailbox-mode minimail-message-mode)
  (minimail-next-message (- count)))

(defun minimail-quit-windows (&optional kill) ;FIXME: use quit-window-hook instead
  (interactive "P" minimail-mailbox-mode minimail-message-mode)
  (-with-associated-buffer mailbox
    (when-let* ((msgbuf (alist-get 'message-buffer -local-state))
                (window (get-buffer-window msgbuf)))
      (quit-restore-window window (if kill 'kill 'bury)))
    (when-let* ((window (get-buffer-window)))
      (quit-window kill window))))

;;;; Sorting by thread

(defun -thread-position (uid)
  "Position of UID in the thread tree when regarded as a flat list."
  (let ((i 0))
    (named-let recur ((tree -thread-tree))
      (pcase (car tree)
        ((pred null))
        ((pred (eq uid)) i)
        ((pred numberp) (cl-incf i) (recur (cdr tree)))
        (subtree (or (recur subtree) (recur (cdr tree))))))))

(defun -thread-root (uid)
  "The root of the thread to which the given UID belongs."
  (named-let recur ((root nil) (tree -thread-tree))
    (pcase (car tree)
      ((pred null))
      ((pred (eq uid)) (or root uid))
      ((and (pred numberp) n) (recur (or root n) (cdr tree)))
      (subtree (or (recur root subtree) (recur root (cdr tree)))))))

(defun -thread-level (uid)
  "The nesting level of UID in the thread tree."
  (named-let recur ((level 0) (tree -thread-tree))
    (pcase (car tree)
      ((pred null) nil)
      ((pred (eq uid)) level)
      ((pred numberp) (recur (1+ level) (cdr tree)))
      (subtree (or (recur level subtree) (recur level (cdr tree)))))))

(defun -thread-subject-prefix (uid)
  "A prefix added to message subjects when sorting by thread."
  (make-string (* 2 (or (-thread-level uid) 0)) ?\s))

(defun -thread-by-subject (messages)
  "Compute a message thread tree from MESSAGES based on subject strings.
This is the ORDEREDSUBJECT algorithm described in RFC 5256.  The return
value is as described in loc. cit. §4, with message UIDs as tree leaves."
  (let* ((hash (make-hash-table :test #'equal))
         (threads (progn
                    (dolist (msg messages)
                      (let-alist msg
                        (push msg (gethash (-base-subject (or .envelope.subject ""))
                                           hash))))
                    (mapcar (lambda (thread) (sort thread :key #'-message-timestamp))
                            (hash-table-values hash))))
         (sorted (sort threads :key (lambda (v) (-message-timestamp (car v))))))
    (mapcar (lambda (thread)
              (cons (let-alist (car thread) .uid)
                    (mapcar (lambda (v) (let-alist v (list .uid))) (cdr thread))))
            sorted)))

(defun minimail-sort-by-thread (&optional descending)
  "Sort messages with grouping by threads.

Within a thread, sort each message after its parents.  Across threads,
preserve the existing order, in the sense that thread A sorts before
thread B if some message from A comes before all messages of B.  This
makes sense when the current sort order is in the “most relevant at top”
style.  If DESCENDING is non-nil, use the opposite convention."
  (interactive nil minimail-mailbox-mode)
  (let* ((table (or (vtable-current-table)
                    (user-error "No table under point")))
         (mhash (make-hash-table)) ;maps message id -> root id and position within thread
         (rhash (make-hash-table)) ;maps root id -> position across threads
         (lessp (lambda (o1 o2)
                  (pcase-let ((`(,ri . ,pi) (gethash (let-alist o1 .uid) mhash))
                              (`(,rj . ,pj) (gethash (let-alist o2 .uid) mhash)))
                    (if (eq ri rj)
                        (< pi pj)
                      (< (gethash ri rhash)
                         (gethash rj rhash))))))
         objects)
    (save-excursion
      ;; Get objects in current sort order (unlike `vtable-objects').
      (goto-char (vtable-beginning-of-table))
      (while-let ((obj (vtable-current-object)))
        (push obj objects)
        (forward-line)))
    (cl-callf nreverse objects)
    (dolist (obj objects)
      (let* ((count (hash-table-count mhash))
             (msgid (let-alist obj .uid))
             (rootid (or (-thread-root msgid) -1))
             (pos (or (-thread-position msgid) -1)))
        (puthash msgid (cons rootid pos) mhash)
        (if descending
            (puthash rootid count rhash)
          (cl-callf (lambda (i) (or i count)) (gethash rootid rhash)))))
    (setf (vtable-objects table) (sort objects :lessp lessp :in-place t))
    ;; Little hack to force vtable to redisplay with our new sorting.
    (cl-letf (((vtable-sort-by table) nil))
      (vtable-revert-command))))

;;; Message buffer

(defvar-keymap minimail-message-mode-map
  :doc "Keymap for Help mode."
  :parent (make-composed-keymap button-buffer-map special-mode-map)
  "n" #'minimail-next-message
  "p" #'minimail-previous-message
  "r" #'minimail-reply
  "R" #'minimail-reply-all
  "f" #'minimail-forward
  "s" #'minimail-search
  "SPC" #'minimail-message-scroll-up
  "S-SPC" #'minimail-message-scroll-down
  "DEL" #'minimail-message-scroll-down)

(define-derived-mode minimail-message-mode special-mode
  '("Message" -mode-line-suffix)
  "Major mode for email messages."
  :interactive nil
  (setq buffer-undo-list t)
  (add-hook 'kill-buffer-hook #'-cleanup-mime-handles nil t))

(defun -message-buffer-name (account mailbox uid)
  (format "%s:%s[%s]" account mailbox uid))

(defun -render-message ()
  "Render message in current buffer using the Gnus machinery."
  ;; Based on mu4e-view.el
  (let* ((ct (mail-fetch-field "Content-Type"))
         (ct (and ct (mail-header-parse-content-type ct)))
         (charset (intern-soft (mail-content-type-get ct 'charset)))
         (charset (if (and charset (coding-system-p charset))
                      charset
                    (detect-coding-region (point-min) (point-max) t))))
    (setq-local
     nobreak-char-display nil
     gnus-newsgroup-charset charset
     gnus-blocked-images "."            ;FIXME: make customizable
     gnus-article-buffer (current-buffer)
     gnus-summary-buffer nil
     gnus-article-wash-types nil
     gnus-article-image-alist nil)
    ;; just continue if some of the decoding fails.
    (ignore-errors (run-hooks 'gnus-article-decode-hook))
    (setq gnus-article-decoded-p gnus-article-decode-hook)
    (save-restriction
      (message-narrow-to-headers-or-head)
      (setf (alist-get 'references -local-state)
            (message-fetch-field "references"))
      (setf (alist-get 'message-id -local-state)
            (message-fetch-field "message-id" t)))
    (gnus-display-mime)
    (when gnus-mime-display-attachment-buttons-in-header
      (gnus-mime-buttonize-attachments-in-header))
    (when-let* ((window (get-buffer-window gnus-article-buffer)))
      (set-window-point window (point-min)))
    (set-buffer-modified-p nil)))

(defun -message-window-adjust-height (window)
  "Try to resize a message WINDOW sensibly.
If the window above it is a mailbox window, make the message window
occupy 3/4 of the available height, but without making the mailbox
window shorter than 6 lines."
  (when-let* ((otherwin (window-in-direction 'above window))
              (otherbuf (window-buffer otherwin)))
    (when (with-current-buffer otherbuf
            (derived-mode-p #'minimail-mailbox-mode))
      (let* ((h1 (window-height window))
             (h2 (window-height otherwin))
             (h3 (max 6 (round (* 0.25 (+ h1 h2))))))
        (adjust-window-trailing-edge otherwin (- h3 h2))))))

(defvar -display-message-base-action
  `((display-buffer-reuse-window
     display-buffer-in-direction)
    (direction . below)
    (window-height . -message-window-adjust-height)))

(defun -cleanup-mime-handles ()
  (mm-destroy-parts gnus-article-mime-handles)
  (setq gnus-article-mime-handles nil)
  (setq gnus-article-mime-handle-alist nil))

(defun -erase-message-buffer ()
  (erase-buffer)
  (dolist (ov (overlays-in (point-min) (point-max)))
    (delete-overlay ov))
  (-cleanup-mime-handles))

(defun -message-mode-advice (newfn)
  (lambda (fn &rest args)
    (apply (if (derived-mode-p 'minimail-message-mode) newfn fn) args)))

(advice-add #'gnus-msg-mail :around
            (-message-mode-advice #'message-mail) ;FIXME: only works if message-mail-user-agent is set
            '((name . -gnus-msg-mail)))

(advice-add #'gnus-button-reply :around
            (-message-mode-advice #'message-reply) ;FIXME: same
            '((name . -gnus-button-reply)))

(defun -display-message (account mailbox uid)
  (let ((buffer (current-buffer)))
    (unless (derived-mode-p #'minimail-message-mode)
      (let ((inhibit-read-only t))
        (erase-buffer)
        (minimail-message-mode)))
    (setq -mode-line-suffix ":Loading")
    (setf (alist-get 'next-message -local-state)
          (list account mailbox uid))
    (athunk-run
     (athunk-let*
         ((msgbuf <- (athunk-condition-case err
                         (-afetch-message account mailbox uid)
                       (t (with-current-buffer buffer
                            (setq -mode-line-suffix ":Error"))
                          (signal (car err) (cdr err))))))
       (when (buffer-live-p buffer)
         (with-current-buffer buffer
           (when (equal (alist-get 'next-message -local-state)
                        (list account mailbox uid))
             (let ((inhibit-read-only t))
               (setq -mode-line-suffix nil)
               (setq -current-account account)
               (setq -current-mailbox mailbox)
               (-erase-message-buffer)
               (rename-buffer (-message-buffer-name account mailbox uid) t)
               (insert-buffer-substring msgbuf)
               (-render-message)))))))
    (display-buffer buffer -display-message-base-action)))

(defun minimail-message-scroll-up (arg &optional reverse)
  (interactive "^P" minimail-message-mode minimail-mailbox-mode)
  (-with-associated-buffer message
    (condition-case nil
        (when-let* ((window (get-buffer-window)))
          (with-selected-window window
            (funcall (if reverse #'scroll-down-command #'scroll-up-command)
                     arg)))
      (t (-with-associated-buffer mailbox
           (minimail-next-message
            (funcall (if reverse '- '+)
                     (cl-signum (prefix-numeric-value arg)))))))))

(defun minimail-message-scroll-down (arg)
  (interactive "^P" minimail-message-mode)
  (minimail-message-scroll-up arg t))

(defun minimail-reply (cite &optional to-address wide)
  (interactive (list (xor current-prefix-arg minimail-reply-cite-original))
               minimail-message-mode
               minimail-mailbox-mode)
  (-with-associated-buffer message     ;FIXME: in mailbox mode, should
                                       ;reply to message at point, not
                                       ;the currently displayed one
    (when-let* ((window (get-buffer-window)))
      (select-window window))
    (let ((message-mail-user-agent 'minimail)
          (message-reply-buffer (current-buffer))
          (msgid (alist-get 'message-id -local-state))
          (refs (alist-get 'references -local-state)))
      (message-reply to-address wide)
      (when msgid
        (save-excursion
          (goto-char (point-min))
          (insert "In-Reply-To: " msgid ?\n)
          (insert "References: ")
          (when refs (insert refs ?\s))
          (insert msgid ?\n)
          (narrow-to-region (point) (point-max))))
      (when cite (message-yank-original)))))

(defun minimail-reply-all (cite &optional to-address)
  (interactive (list (xor current-prefix-arg minimail-reply-cite-original))
               minimail-message-mode
               minimail-mailbox-mode)
  (minimail-reply cite to-address t))

(defun minimail-forward ()
  (interactive nil minimail-message-mode minimail-mailbox-mode)
  (-with-associated-buffer message
    (when-let* ((window (get-buffer-window)))
      (select-window window))
    (let ((message-mail-user-agent 'minimail))
      (message-forward))))

;;; MUA definition

;;;###autoload
(define-mail-user-agent 'minimail
  #'minimail-message-mail
  #'message-send-and-exit
  #'message-kill-buffer
  'message-send-hook)

(defun -send-mail-via-smtpmail ()
  "Call `smtpmail-send-it' with parameters from the X-Minimail-Account header."
  (let ((account (save-restriction
                   (message-narrow-to-headers-or-head)
                   (mail-fetch-field "X-Minimail-Account"
                                     nil nil nil t))))
    (let* ((props (or (alist-get (intern-soft account) minimail-accounts)
                      (user-error "Invalid Minimail account: %s" account)))
           (url (url-generic-parse-url (plist-get props :outgoing-url)))
           (smtpmail-store-queue-variables t)
           (smtpmail-smtp-server (url-host url))
           (smtpmail-smtp-user (cond ((url-user url) (url-unhex-string (url-user url)))
                                     ((plist-get props :mail-address))))
           (smtpmail-stream-type (pcase (url-type url)
                                   ("smtps" 'tls)
                                   ("smtp" 'starttls)
                                   (other (user-error "\
In `minimail-accounts', outgoing-url must have smtps or smtp scheme, got %s" other))))
           (smtpmail-smtp-service (or (url-portspec url)
                                      (pcase smtpmail-stream-type
                                        ('tls 465)
                                        ('starttls 587)))))
      (smtpmail-send-it))))

;;;###autoload
(defun minimail-message-mail (&optional to subject &rest rest)
  (pcase-let*
      ((`(,account . ,props)
        (or (seq-some (lambda (it)
                        (when (plist-member (cdr it) :outgoing-url) it))
                      `(,(assq -current-account minimail-accounts)
                        ,@minimail-accounts))
            (user-error "No mail account has been configured to send messages")))
       (setup (lambda ()
                (setq-local
                 user-full-name (or (plist-get props :full-name)
                                    user-full-name)
                 user-mail-address (or (plist-get props :mail-address)
                                       user-mail-address)
                 message-signature (or (plist-get props :signature)
                                       message-signature)
                 message-signature-file (or (plist-get props :signature-file)
                                            message-signature-file)))))
    (let ((message-mail-user-agent 'message-user-agent)
          (message-mode-hook (cons setup message-mode-hook)))
      (apply #'message-mail to subject rest))
    (setq-local message-send-mail-function #'-send-mail-via-smtpmail)
    (message-add-header (format "X-Minimail-Account: %s" account))
    (message-sort-headers)
    (cond
     ((not to) (message-goto-to))
     ((not subject) (message-goto-subject))
     (t (message-goto-body)))
    t))

;;; Completion framework integration

;;;; Vertico

(defvar vertico--input)

(defun -minibuffer-update-vertico ()
  (declare-function vertico--exhibit "ext:vertico")
  (when vertico--input
    (setq vertico--input t)
    (vertico--exhibit)))

(with-eval-after-load 'vertico
  (add-hook '-minibuffer-update-hook #'-minibuffer-update-vertico))

;;;; Mct

(with-eval-after-load 'mct
  (add-hook '-minibuffer-update-hook 'mct--live-completions-refresh))

;; Local Variables:
;; read-symbol-shorthands: (("-" . "minimail--") ("athunk-" . "minimail--athunk-"))
;; End:

(provide 'minimail)
;;; minimail.el ends here
