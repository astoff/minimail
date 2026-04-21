;;; minimail.el --- Simple, non-blocking IMAP email client  -*- lexical-binding: t; -*-

;; Copyright (C) 2026  Free Software Foundation, Inc.

;; Author: Augusto Stoffel <arstoffel@gmail.com>
;; Keywords: mail
;; URL: https://codeberg.org/astoff/minimail
;; Package-Requires: ((emacs "30.1") (transient "0.12"))
;; Version: 0.4.2

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
(require 'transient)
(require 'tree-widget)
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

(defmacro athunk--λ (args &rest body)
  "Like `lambda', but sneak location of definition in the docstring."
  (declare (indent 1))
  `(lambda ,args
     ,(when-let* ((pos (byte-compile--warning-source-offset)))
        (save-excursion
          (goto-char pos)
          (format "%s:%s:%s"
                  (file-name-nondirectory byte-compile-current-file)
                  (1+ (count-lines (point-min) (pos-bol)))
                  (1+ (current-column)))))
     ,(macroexp-progn body)))

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
                   (athunk--λ (,esym ,vsym)
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
        (run-with-timer
         0 nil (pop athunks)
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
    `(lambda (,csym)
       (funcall ,form
                (lambda (,esym ,vsym)
                  (condition-case ,hsym
                      (condition-case ,var
                          (if ,esym (signal ,esym ,vsym) ,vsym)
                        ,@handlers)
                    (:success (funcall ,csym nil ,hsym))
                    (t (funcall ,csym (car ,hsym) (cdr ,hsym)))))))))

(defmacro athunk-ignore-errors (&rest body)
  "Like `ignore-errors', but for asynchronous code."
  (declare (indent 0))
  `(athunk-condition-case nil ,(macroexp-progn body) (error nil)))

(defun athunk--semaphore (state athunk priority)
  (lambda (cont)
    (let ((task (lambda ()
                  (funcall athunk
                           (lambda (err val)
                             (if-let* ((next (pop (cdr state))))
                                 (run-with-timer 0 nil next)
                               (cl-incf (car state)))
                             (funcall cont err val))))))
      (cond
       ((> (car state) 0) (cl-decf (car state)) (funcall task))
       (priority (push task (cdr state)))
       (t (nconc state (list task)))))))

(cl-defmacro athunk-with-semaphore (place athunk &key (concurrency 1) use-lifo-queue)
  "Return an athunk which acquires a semaphore then runs ATHUNK.
Note that the expression ATHUNK is evaluated before acquiring the
semaphore.

PLACE is a generalized variable pointing to the semaphore state.  It is
initialized automatically."
  (declare (indent 1))
  `(athunk--semaphore (with-memoization ,place (list ,concurrency))
                      ,athunk
                      ,use-lifo-queue))

(cl-defun athunk-run-polling (athunk &key
                                     (message nil)
                                     (interval 1)
                                     (max-tries -1))
  "Run ATHUNK, polling every INTERVAL seconds and blocking until done.
Give up after MAX-TRIES, if that is non-negative.
If MESSAGE is non-nil, show a progress reporter, but only if the
athunk doesn't resolve immediately."
  (let (done err val reporter)
    (funcall athunk (lambda (e v) (setq done t err e val v)))
    (while (not (or done (zerop max-tries)))
      (cond
       (reporter (progress-reporter-update reporter))
       (message (setq reporter (make-progress-reporter message))))
      (cl-decf max-tries)
      (sleep-for interval))
    (when err (signal err val))
    (unless done (error "athunk timed out"))
    (when reporter (progress-reporter-done reporter))
    val))

;;; Customizable options

(defgroup minimail nil
  "Simple, non-blocking IMAP email client."
  :prefix "minimail-"
  :group 'mail)

(cl-defun -custom-type-query-alist (&key key-type value-type allow-single value)
  (let* ((kt (pcase-exhaustive key-type
               ('mailbox '(choice
                           (const :tag "Default" t)
                           (const :tag "\"All Mail\" mailbox" \\All)
                           (const :tag "\"Archive\" mailbox" \\Archive)
                           (const :tag "\"Drafts\" mailbox" \\Drafts)
                           (const :tag "\"Important\" mailbox" \\Flagged)
                           (const :tag "\"Junk\" mailbox" \\Junk)
                           (const :tag "\"Sent\" mailbox" \\Sent)
                           (const :tag "\"Trash\" mailbox" \\Trash)
                           (string :tag "Specific mailbox")
                           (list :tag "Mailboxes matching regexp"
                                 (const regexp) regexp)
                           (sexp :tag "Complex selector")))
               ('flag '(choice
                        (const :tag "Default" t)
                        (const :tag "Unseen" (not \\Seen))
                        (const :tag "Flagged (a.k.a. Starred)" \\Flagged)
                        (const :tag "Important" (or $Important \\Important))
                        (const :tag "Answered" \\Answered)
                        (const :tag "Forwarded" $Forwarded)
                        (const :tag "Phishing" $Phishing)
                        (const :tag "Junk" $Junk)
                        (sexp :tag "Complex selector")))))
         (alist `(alist :key-type ,kt :value-type ,value-type)))
    (if allow-single
        `(choice :tag "Scope"
                 :value ,value
                 ,value-type
                 (alist :tag "Mailbox-specific values"
                        :match ,(lambda (_ v) (consp v))
                        ,@(cdr alist)))
      alist)))

(defcustom minimail-reply-cite-original t
  "Whether to cite the original message when replying."
  :type 'boolean)

(defcustom minimail-connection-idle-timeout 60
  "Time in seconds a network connection can remain open without activity."
  :type 'boolean)

(defcustom minimail-message-cache-size 20
  "Maximum number of messages to keep cached in memory."
  :type 'natnum)

(defcustom minimail-mailbox-mode-columns
  '((\\Sent flag-flagged flag-answered date recipients subject)
    (t flag-flagged flag-answered date from subject))
  "Columns to display in `minimail-mailbox-mode' buffers.
This is an alist mapping mailbox selectors to lists of column names as
defined in `minimail-mailbox-mode-column-alist'."
  :type (-custom-type-query-alist
         :key-type 'mailbox
         :value-type '(repeat
                       (choice (const :tag "Message number" id)
                               (const :tag "Seen" flag-seen)
                               (const :tag "Flagged" flag-flagged)
                               (const :tag "Answered" flag-answered)
                               (const :tag "From" from)
                               (const :tag "To" to)
                               (const :tag "Recipients" recipients)
                               (const :tag "Subject" subject)
                               (const :tag "Date" date)
                               (const :tag "Size" size)))))

(defcustom minimail-mailbox-mode-sort-by
  '((t (date . descend) (thread . ascend)))
  "Sorting criteria for `minimail-mailbox-mode' buffers.
This is an alist mapping mailbox selectors to lists of the form

  ((COLUMN . DIRECTION) ...)

COLUMN is a column name, as in `minimail-mailbox-mode-columns'.
DIRECTION is either `ascend' or `descend'.

As a special case, an entry of the form (thread . DIRECTION) enables
sorting by thread."
  :type (-custom-type-query-alist
         :key-type 'mailbox
         :value-type
         `(repeat :tag "Sorting criteria"
                  (cons (choice :tag "Column"
                                (const :tag "Thread" thread)
                                ,@(let* ((v (get 'minimail-mailbox-mode-columns
                                                 'custom-type))
                                         (v (plist-get (cdr v) :value-type)))
                                    (cdadr v)))
                        (choice :tag "Direction"
                                (const ascend)
                                (const descend))))))

(defcustom minimail-fetch-limit 100
  "Maximum number of messages to fetch at a time when displaying a mailbox."
  :type 'natnum)

(defcustom minimail-thread-style 'shallow
  "How to display message threads."
  :type '(choice (const :tag "Shallow" shallow)
                 (const :tag "Hierarchical" hierarchical)
                 (const :tag "Don't compute threads" nil)))

(defcustom minimail-subject-faces '(((not \\Seen) . minimail-unseen)
                                    (t . vtable))
  "Face to apply to subject strings based on the message flags.
This is used in `minimail-mailbox-mode' buffers."
  :type (-custom-type-query-alist :key-type 'flag :value-type 'face))

(defcustom minimail-accounts
  '((yhetil :incoming-url "imaps://:@yhetil.org/yhetil.emacs"
            :thread-style hierarchical))
  "Account configuration for the Minimail client.
This is an alist where keys are names used to refer to each account and
values are a plist with the following information:

:incoming-url
  Information about the IMAP server as a URL. Normally, it suffices to
  enter \"imaps://<server-address>\".  More generally, it can take the
  form

    imaps://<username>:<password>@<server-address>:<port>

  If username is omitted, use the :mail-address property instead.

  If password is omitted (which is highly recommended), use the
  auth-source mechanism. See Info node `(auth) Top' for details.

:outgoing-url
  Information about the SMTP server as a URL.  Normally, it suffices
  to enter \"smtps://<server-address>\", but you can provide more
  details as in :incoming-url.
:mail-address
  The email address of this account.  Overrides the global value of
  `user-mail-address'.

:full-name
  Name used in the To field of messages you compose.  Overrides the
  global value of `user-full-name'.

:signature
  Message signature, as value accepted by `message-signature' or,
  alternatively, (file FILENAME).

:thread-style
  Account or mailbox-specific override for `minimail-thread-style'.

:fetch-limit
  Account or mailbox-specific override for `minimail-fetch-limit'.

:mailbox-columns
  Mailbox-specific override for `minimail-mailbox-mode-columns'.

:mailbox-sort-by
  Mailbox-specific override for `minimail-mailbox-mode-sort-by'.

All entries all optional, except for :incoming-url.

Account or mailbox-specific overrides may be a simple value, which
applies to all mailboxes of the account in question, or an alist
mapping mailbox selectors to a value.

A mailbox selector may be a symbol or string, which means to match
mailbox with that name or IMAP flag.  More complex selectors are
possible, see `minimail--key-match-p'."
  :type
  `(alist
    :key-type (symbol :tag "Account identifier")
    :value-type
    (plist
     :tag "Account properties"
     :options
     ((:incoming-url string)
      (:outgoing-url string)
      (:mail-address    ,(-custom-type-query-alist
                          :allow-single t :value ""
                          :key-type 'mailbox :value-type 'string))
      (:full-name       ,(-custom-type-query-alist
                          :allow-single t :value ""
                          :key-type 'mailbox :value-type 'string))
      (:signature       ,(-custom-type-query-alist
                          :allow-single t
                          :key-type 'mailbox
                          :value-type '(choice
                                        (const :tag "Default" nil)
                                        (function-item :tag "No signature" ignore)
                                        (string :tag "String to insert")
                                        (function :tag "Function to call")
                                        (list :tag "Use signature file"
                                              (const :format "" file) file))))
      (:thread-style    ,(-custom-type-query-alist
                          :allow-single t
                          :key-type 'mailbox
                          :value-type (get 'minimail-thread-style 'custom-type)))
      (:fetch-limit     ,(-custom-type-query-alist
                          :allow-single t :value 100
                          :key-type 'mailbox :value-type 'natnum))
      (:mailbox-columns ,(-custom-type-query-alist
                          :allow-single t
                          :key-type 'mailbox
                          :value-type (plist-get
                                       (cdr (get 'minimail-mailbox-mode-columns
                                                 'custom-type))
                                       :value-type)))
      (:mailbox-sort-by ,(-custom-type-query-alist
                          :allow-single t
                          :key-type 'mailbox
                          :value-type (plist-get
                                       (cdr (get 'minimail-mailbox-mode-sort-by
                                                 'custom-type))
                                       :value-type)))))))

;;;; Faces

(defgroup minimail-faces nil
  "Faces used by Minimail."
  :group 'minimail
  :group 'faces)

(defface minimail-unseen '((t :weight bold :inherit vtable))
  "Face to indicate unseen messages.")

(defface minimail-mode-line-loading nil
  "Face to indicate a background operation in the mode line.")

(defface minimail-mode-line-error '((t :inherit error))
  "Face to indicate an error in the mode line.")

(defface minimail-line-drawing '((t :inherit default))
  "Face used for drawings such as thread trees.")

;;;; Icons

(defgroup minimail-icons nil
  "Icons used by Minimail."
  :group 'minimail)

(define-icon minimail-mailbox nil
  '((emoji "🗂️") (text ""))
  "Generic icon for mailboxes."
  :version "0.3")

(define-icon minimail-mailbox-closed minimail-mailbox
  '((emoji "📁") (symbol "⊞ ")(text "[+]"))
  "Icon for mailboxes with children, when closed."
  :version "0.3")

(define-icon minimail-mailbox-open minimail-mailbox
  '((emoji "📂") (symbol "⊟ ") (text "[-]"))
  "Icon for mailboxes with children, when open."
  :version "0.3")

(define-icon minimail-mailbox-archive minimail-mailbox
  '((emoji "🗃️"))
  "Icon for archive mailboxes."
  :version "0.3")

(define-icon minimail-mailbox-drafts minimail-mailbox
  '((emoji "📝"))
  "Icon for drafts mailboxes."
  :version "0.3")

(define-icon minimail-mailbox-flagged minimail-mailbox
  '((emoji "⭐"))
  "Icon for flagged mailboxes."
  :version "0.3")

(define-icon minimail-mailbox-important minimail-mailbox
  '((emoji "🔶"))
  "Icon for important mailboxes."
  :version "0.3")

(define-icon minimail-mailbox-inbox minimail-mailbox
  '((emoji "📥"))
  "Icon for inbox mailboxes."
  :version "0.3")

(define-icon minimail-mailbox-junk minimail-mailbox
  '((emoji "♻️"))
  "Icon for junk mailboxes."
  :version "0.3")

(define-icon minimail-mailbox-sent minimail-mailbox
  '((emoji "📤"))
  "Icon for sent mailboxes."
  :version "0.3")

(define-icon minimail-mailbox-trash minimail-mailbox
  '((emoji "🗑️"))
  "Icon for trash mailboxes."
  :version "0.3")

(define-icon minimail-message-unseen nil
  '((emoji "✉️") (symbol "●") (text "."))
  "Icon for unseen messages."
  :help-echo "Unseen"
  :version "0.3")

(define-icon minimail-message-flagged nil
  '((emoji "⭐") (symbol "★") (text "!"))
  "Icon for flagged messages."
  :help-echo "Flagged"
  :version "0.3")

(define-icon minimail-message-important nil
  '((emoji "🔸") (symbol "⬥") (text "i"))
  "Icon for important messages."
  :help-echo "Important"
  :version "0.3")

(define-icon minimail-message-answered nil
  '((emoji "↩️") (symbol "↩") (text "A"))
  "Icon for answered messages."
  :help-echo "Answered"
  :version "0.3")

(define-icon minimail-message-forwarded nil
  '((emoji "➡️") (symbol "→") (text "F"))
  "Icon for answered messages."
  :help-echo "Forwarded"
  :version "0.3")

(define-icon minimail-message-junk nil
  '((emoji "♻️") (symbol "♻") (text "J"))
  "Icon for junk messages."
  :help-echo "Junk"
  :version "0.3")

(define-icon minimail-message-phishing nil
  '((emoji "⚠️") (symbol "⚠") (text "J" :face warning))
  "Icon for phishing messages."
  :help-echo "Phishing"
  :version "0.3")

(define-icon minimail-thread-leaf-terminal nil
  '((symbol "└─ " :face minimail-line-drawing)
    (text "`-- " :face minimail-line-drawing))
  "Tree-drawing symbol for a leaf which is last among its siblings."
  :version "0.4")

(define-icon minimail-thread-leaf-nonterminal nil
  '((symbol "├─ " :face minimail-line-drawing)
    (text "|-- " :face minimail-line-drawing))
  "Tree-drawing symbol for leaf which is not last among its siblings."
  :version "0.4")

(define-icon minimail-thread-parent-terminal nil
  '((symbol "   " :face minimail-line-drawing)
    (text "    " :face minimail-line-drawing))
  "Tree-drawing symbol for a parent which is last among its siblings."
  :version "0.4")

(define-icon minimail-thread-parent-nonterminal nil
  '((symbol "│  " :face minimail-line-drawing)
    (text "|   " :face minimail-line-drawing))
  "Tree-drawing symbol for a parent which is not last among its siblings."
  :version "0.4")

(define-icon minimail-thread-false-root nil
  '((text ""))
  "Tree-drawing symbol for a thread root that is a reply."
  :version "0.4")

;;; Internal variables and helper functions

(defvar -account-state nil
  "Alist mapping accounts to assorted state information about them.")

(defvar-local -local-state nil
  "Place to store assorted buffer-local information.")

(defvar-local -current-mailbox nil
  "The mailbox corresponding to the current buffer.
In mailbox and message buffers, this variable holds a cons cell
(ACCOUNT . MAILBOX-NAME) of a symbol and a string and is the data
expected as MAILBOX argument of many functions.

In IMAP process buffers, this variable holds the name of the selected
mailbox, or nil when the connection is in unselected state.")

(defvar-local -message-list nil)

(defvar -minibuffer-update-hook nil
  "Hook run when minibuffer completion candidates are updated.")

(defvar -message-rendering-function #'-gnus-render-message
  "Function used to render a message buffer for display.")

(define-error '-imap-error "error in IMAP response")

(defun -get-data (string)
  "Get data stored as a string property in STRING."
  (cl-assert (stringp string))
  (get-text-property 0 'minimail string))

(defvar -logging-options nil
  "Whether to log server responses and other debug information.")

(defun -log-message-1 (args)
  "Helper function for `minimail--log-message'.
ARGS is the entire argument list of `minimail--log-message'."
  (let* ((props (ensure-list -logging-options))
         (maxsize (plist-get props :max-size))
         (bufname (or (plist-get props :buffer-name) "*minimail-log*"))
         (buffer (or (get-buffer bufname)
                     (with-current-buffer (get-buffer-create bufname)
                       (view-mode)
                       (setq-local outline-regexp "")
                       (setq buffer-undo-list t)
                       (current-buffer)))))
    (with-current-buffer buffer
      (save-excursion
        (goto-char (point-max))
        (let ((inhibit-read-only t)
              (start (point)))
          (insert (format-time-string "[%T] "))
          (put-text-property start (1+ start) 'invisible t)
          (put-text-property start (point) 'face 'warning)
          (insert (apply #'format args))
          (unless (eq (char-before) ?\n) (insert ?\n))
          (goto-char start)
          (while (re-search-forward "{\\([0-9]+\\)}\r\n" nil t)
            (let* ((start (prog1 (point)
                            (forward-char (string-to-number (match-string 1)))))
                   (ov (make-overlay start (point))))
              (overlay-put ov 'display (buttonize "[...]" #'delete-overlay ov
                                                  "Show literal data"))))
          (when maxsize
            (goto-char (- (point-max) maxsize))
            (delete-region (point-min) (pos-bol))))))))

(defmacro -log-message (string &rest args)
  "Write a message to buffer pointed by `minimail--log-buffer', if non-nil.
The message is formed by calling `format' with STRING and ARGS."
  `(when -logging-options (-log-message-1 (list ,string ,@args))))

(defvar minimail-mailbox-history nil
  "History variable for mailbox selection.")

(defun -mailbox-display-name (mailbox)
  "String identifying MAILBOX, used e.g. as a buffer name."
  (format "%s:%s" (car mailbox) (cdr mailbox)))

(defun -key-match-p (condition key)
  "Check whether KEY satisfies CONDITION.
KEY is a string or list of strings."
  (pcase-exhaustive condition
    ('t t)
    ((or (pred symbolp) (pred stringp))
     (if (listp key) (assoc-string condition key) (string= condition key)))
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

(defun -settings-scalar-get (keyword account-or-mailbox)
  "Retrieve the most specific configuration value for KEYWORD.

ACCOUNT-OR-MAILBOX may be a symbol identifying an account or a cons
cell (ACCOUNT . MAILBOX-NAME).  We then proceed as follows:

1. Start looking up `minimail-accounts' -> ACCOUNT -> KEYWORD.
   a. If the entry exists and is not an alist, return it.
   b. If it is an alist, look up MAILBOX-NAME in it and return the
      associated value.
2. If not found and KEYWORD has a fallback variable associated to it,
   return its value.
3. Else, return nil."
  (let* ((acct (or (car-safe account-or-mailbox) account-or-mailbox))
         (mbname (cdr-safe account-or-mailbox))
         (found (plist-member (alist-get acct minimail-accounts) keyword))
         (val (cadr found)))
    (when (consp (car-safe val)) ;it's a query alist
      (let ((key (when mbname
                   (cons mbname (-mailbox-flags (cons acct mbname))))))
        (setq found (-assoc-query key val))
        (setq val (cdr found))))
    (if found val
      (symbol-value
       (alist-get keyword
                  '((:fetch-limit . minimail-fetch-limit)
                    (:full-name . user-full-name)
                    ;; Unlike other keywords, we care to distinguish
                    ;; when this one is explicitly set
                    ;; (:mail-address . user-mail-address)
                    (:signature . message-signature)
                    (:thread-style . minimail-thread-style)))))))

(defun -settings-alist-get (keyword mailbox)
  "Retrieve the most specific configuration value for KEYWORD.

MAILBOX should be a cons cell of the form (ACCOUNT . MAILBOX-NAME).
Inspect `minimail-accounts' -> ACCOUNT -> KEYWORD, which should be an
alist; if it contains a key matching MAILBOX-NAME, return that value.

Otherwise, if KEYWORD has an associated fallback variable, look up
MAILBOX-NAME in it."
  (let* ((acct (car mailbox))
         (flags (-mailbox-flags mailbox))
         (keys (cons (cdr mailbox) flags)))
    (if-let* ((alist (plist-get (alist-get acct minimail-accounts) keyword))
              (val (-assoc-query keys alist)))
        (cdr val)
      (let* ((vars '((:mailbox-columns . minimail-mailbox-mode-columns)
                     (:mailbox-sort-by . minimail-mailbox-mode-sort-by)))
             (var (alist-get keyword vars)))
        (-alist-query mailbox (symbol-value var))))))

(defun -alist-merge (&rest alists)
  "Merge ALISTS keeping only the first occurrence of each key."
  (let (seen result)
    (dolist (alist alists)
      (dolist (it alist)
        (unless (memq (car it) seen)
          (push (car it) seen)
          (push it result))))
    (nreverse result)))

(defun -set-mode-line-suffix (state)
  (setq mode-line-process
        (pcase state
          ('loading
           `(":" (:propertize "Loading"
                              face minimail-mode-line-loading)))
          (`(,error . ,data)
           `(":" (:propertize "Error"
                              help-echo ,(format "%s: %s" error data)
                              face minimail-mode-line-error))))))
;;;; vtable tricks

(defun -vtable-ensure-table ()
  "Return table under point or signal an error.
But first move point inside table if near the end of buffer."
  (or (vtable-current-table)
      (and (text-property-search-backward 'vtable nil t)
           (forward-line -1)
           (vtable-current-table))
      (user-error "No table found")))

(defun -vtable-find-object (pred &optional below)
  "Go to the first object satisfying PRED in the current table.
Return the object, or nil if not found.
If BELOW is non-nil, only search starting from the current position."
  (let ((start (point)))
    (unless below (vtable-beginning-of-table))
    (while (when-let* ((obj (vtable-current-object)))
             (not (funcall pred obj)))
      (forward-line))
    (or (vtable-current-object)
        (prog1 nil (goto-char start)))))

(defvar -vtable-before-sort-by-current-column-hook nil)
(advice-add #'vtable-sort-by-current-column :before
            (lambda (&rest _)
              (run-hooks '-vtable-before-sort-by-current-column-hook))
            '((name . -vtable-before-sort-by-current-column-hook)))

;;; Low-level IMAP communication

;; References:
;; - IMAP4rev1: https://datatracker.ietf.org/doc/html/rfc3501
;; - IMAP4rev2: https://datatracker.ietf.org/doc/html/rfc9051
;; - IMAP URL syntax: https://datatracker.ietf.org/doc/html/rfc5092

(defvar-local -imap-callbacks nil)
(defvar-local -imap-command-queue nil)
(defvar-local -imap-idle-timer nil)
(defvar-local -imap-last-tag nil)

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
         (user (or (when (url-user url)
                      (url-unhex-string (url-user url)))
                   (-settings-scalar-get :mail-address account)
                   (user-error "No username found for account %s" account)))
         (pass (or (url-password url)
                   (let ((enable-recursive-minibuffers t))
                     (auth-source-pick-first-password
                      :user user
                      :host (url-host url)
                      :port (url-portspec url)
                      ;; TODO: Offer to save, if authentication successful.
                      :create t))
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
    (set-process-filter proc #'-imap-process-filter)
    (set-process-sentinel proc #'-imap-process-sentinel)
    (set-process-query-on-exit-flag proc nil)
    (with-current-buffer buffer
      (set-buffer-multibyte nil)
      (setq -imap-last-tag 0)
      (setq -imap-idle-timer (run-with-timer
                              minimail-connection-idle-timeout nil
                              #'delete-process proc)))
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

(defun -imap-process-filter (proc string)
  (with-current-buffer (process-buffer proc)
    (timer-set-time -imap-idle-timer
                    (time-add nil minimail-connection-idle-timeout))
    (save-excursion
      (goto-char (point-max))
      (insert string))
    (cond
     ;; Case 1: we are in the process of receiving an IMAP literal
     ;; string.  Keep point at the beginning of the literal string to
     ;; check again next time if it's complete.  If this test fails,
     ;; then as a side effect we skip over any complete literal
     ;; strings that may be present in the buffer.
     ((catch 'done
        (while (re-search-forward "{\\([0-9]+\\)}\r\n" nil t)
          (let ((end (+ (point) (string-to-number (match-string 1)))))
            (if (<= end (point-max))
                (goto-char end)
              (goto-char (match-beginning 0))
              (throw 'done t))))))
     ;; Case 2: we find a tagged response.  Call the respective
     ;; callback and send the next command, if there is one in the
     ;; queue.
     ((re-search-forward (rx bol
                             ?T (group (+ digit))
                             ?\s (group (+ alpha))
                             ?\s (group (* (not control)))
                             (? ?\r) ?\n)
                         nil t)
      (pcase-let* ((cont (copy-marker (match-end 0)))
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
            (progn
              (cl-assert (equal mailbox (and mailbox -current-mailbox)) t)
              (with-restriction (point-min) cont
                (goto-char (point-min))
                (funcall callback status message)))
          (delete-region (point-min) cont)
          (when-let* ((queued (pop -imap-command-queue)))
            (apply #'-imap-send proc queued)))))
     ;; Case 3: no tagged response yet.  Look for one again when more
     ;; data arrives.
     (t (goto-char (point-max))
        (goto-char (pos-bol))))))

(defun -imap-send (proc tag mailbox command)
  "Execute an IMAP COMMAND (provided as a string) in network stream PROC.
TAG is an IMAP tag for the command.
Ensure the given MAILBOX is selected before issuing the command, unless
it is nil."
  (if (or (not mailbox)
          (equal mailbox -current-mailbox))
      (process-send-string proc (format "T%s %s\r\n" tag command))
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
      (process-send-string proc (format "T%s SELECT %s\r\n"
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

(defun -imap-quote (s)
  "Make a UTF-7 encoded quoted string as per IMAP spec."
  (when (string-match-p (rx (any control nonascii)) s)
    (setq s (encode-coding-string s 'utf-7-imap)))
  (setq s (replace-regexp-in-string (rx (group (or ?\\ ?\"))) "\\\\\\1" s))
  (concat "\"" s "\""))

(defun -imap-encode-command (string)
  "Encode quoted strings as IMAP literals where needed.
STRING is assumed to be a reasonable IMAP command, except that it may
contain quoted strings with non-ASCII characters."
  (if (not (string-match-p (rx (any control nonascii)) string))
      string
    (with-temp-buffer
      (insert string)
      (goto-char (point-min))
      (while (search-forward "\"" nil t)
        (backward-char)
        (let ((p (point))
              (s (read (current-buffer))))
          (when (string-match-p (rx (any control nonascii)) s)
            (delete-region p (point))
            (insert (format "{%s+}\r\n" (string-bytes s)) s))))
      (buffer-string))))

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
  (tagged    () (bol) (char ?T) (+ [0-9]) sp) ;we always format our tags as T<number>
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
  (astring7  ()
             astring
             `(s -- (if (string-search "&" s) (decode-coding-string s 'utf-7-imap) s)))
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
             sp astring7
             `(f d n -- `(,n (delimiter . ,d) (flags . ,f))))
       (status untagged "STATUS "
               (list astring7 " ("
                     (* (opt sp)
                        (or (and "MESSAGES " number `(n -- `(messages . ,n)))
                            (and "RECENT " number `(n -- `(recent . ,n)))
                            (and "UIDNEXT " number `(n -- `(uid-next . ,n)))
                            (and "UIDVALIDITY " number `(n -- `(uid-validity . ,n)))
                            (and "UNSEEN " number `(n -- `(unseen . ,n)))))
                     ")"))
       (response (list (* (or item status) crlf))))
    (car (peg-run (peg response) #'-imap-parse-error))))

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
       ;; (body "BODY " (or body-single body-multi) `(s -- `(body . ,s)))
       (body "BODY " balanced)
       (content "BODY[] " literal `(start end -- `(content ,start . ,end)))
       (flags "FLAGS (" (list (* (opt sp) flag)) ")"
              `(v -- `(flags . ,v)))
       (x-gm-labels "X-GM-LABELS (" (list (* (opt sp) astring7)) ")"
                    `(v -- `(x-gm-labels . ,v)))
       (thread-id (or (and "THREADID " (or anil (and "(" atom ")")))
                      (and "X-GM-THRID " number))
                  `(v -- `(thread-id . ,v)))
       (email-id (or (and "EMAILID (" atom ")") (and "X-GM-MSGID " number))
                 `(v -- `(email-id . ,v)))
       (internal-date "INTERNALDATE " imapdate
                     `(v -- `(internal-date . ,v)))
       (size "RFC822.SIZE " number `(n -- `(rfc822-size . ,n)))
       (uid "UID " number `(n -- `(uid . ,n)))
       (item untagged number `(n -- `(id . ,n))
             " FETCH ("
             (* (opt sp) (or uid flags size envelope content thread-id x-gm-labels))
             ")" crlf))
    (car-safe
     (peg-run (peg (list (* (list item))))))))

;; Helpers to access message information alists from the FETCH command
(defsubst -message-id (msg) (let-alist msg .id))
(defsubst -message-uid (msg) (let-alist msg .uid))
(defsubst -message-flags (msg) (let-alist msg .flags))
(defsubst -message-envelope (msg) (let-alist msg .envelope))
(defsubst -message-subject (msg) (let-alist msg .envelope.subject))

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

(defun -amake-request (account-or-mailbox command)
  "Issue COMMAND to the IMAP server, ensuring the right mailbox is selected.
ACCOUNT-OR-MAILBOX can be a cons cell (ACCOUNT . MAILBOX-NAME) or just
an account name as a symbol.

Returns an athunk which resolves to a temporary buffer containing the
server response.  The temporary buffer is cleaned up automatically after
being used."
  (lambda (cont)
    (let* ((account (or (car-safe account-or-mailbox) account-or-mailbox))
           (proc (alist-get 'process (alist-get account -account-state))))
      (unless (process-live-p proc)
        (setq proc (-imap-connect account))
        (setf (alist-get 'process (alist-get account -account-state)) proc))
      (-imap-enqueue
       proc (cdr-safe account-or-mailbox) command
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
             (run-with-timer 0 nil continue))))))))

(defun -aget-capability (account)
  (athunk-let*
      ((cached (alist-get 'capability (alist-get account -account-state)))
       (new <- (if cached ;race condition here, but it's innocuous :-)
                   (athunk-wrap nil)
                 (athunk-let*
                     ((buffer <- (-amake-request account "CAPABILITY")))
                   (with-current-buffer buffer
                     (-parse-capability))))))
    (or cached
        (setf (alist-get 'capability (alist-get account -account-state)) new))))

(defun -format-sequence-set (set)
  "Format a set of message IDs as a string.
SET can be a number, t to represent the highest ID, an element of the
form (range START END) or a list of the above.  Ranges, in IMAP fashion,
are 1-based and inclusive of the end."
  (pcase-exhaustive set
    ('t "*")
    ((pred numberp set) (number-to-string set))
    (`(range ,from ,to)
     (concat (-format-sequence-set from) ":" (-format-sequence-set to)))
    ((pred (not null))
     (mapconcat #'-format-sequence-set set ","))))

(defvar -aget-mailbox-listing nil
  "Synchronization data for the function of same name.")

(defun -aget-mailbox-listing (account &optional refresh)
  (athunk-with-semaphore (alist-get account -aget-mailbox-listing)
    (athunk-let*
        ((cached (unless refresh
                   (alist-get 'mailboxes (alist-get account -account-state))))
         (new <- (if cached
                     (athunk-wrap nil)
                   (athunk-let*
                       ((props (alist-get account minimail-accounts))
                        (url (url-generic-parse-url (plist-get props :incoming-url)))
                        (path (string-remove-prefix "/" (car (url-path-and-query url))))
                        (caps <- (-aget-capability account))
                        (return (delq nil (list (when (memq 'special-use caps)
                                                  "SPECIAL-USE")
                                                (when (memq 'list-status caps)
                                                  "STATUS (MESSAGES UIDNEXT UNSEEN)"))))
                        (cmd (format (if return "LIST %s * RETURN (%s)" "LIST %s *")
                                     (-imap-quote path)
                                     (string-join return " ")))
                        (buffer <- (-amake-request account cmd)))
                     (with-current-buffer buffer
                       (mapcar (pcase-lambda (`(,k . ,v)) `(,k . ,(mapcan #'cdr v)))
                               (seq-group-by #'car (-parse-list))))))))
      (or cached
          (setf (alist-get 'mailboxes (alist-get account -account-state)) new)))))

(defun -mailbox-flags (mailbox)
  "Return the MAILBOX flags, as a list of strings."
  ;; This should actually never block, since if we know the mailbox we
  ;; must already have fetched the mailbox listing.
  (athunk-run-polling
   (athunk-let* ((mailboxes <- (-aget-mailbox-listing (car mailbox))))
     (alist-get 'flags (assoc (cdr mailbox) mailboxes)))
   :message "Fetching mailbox information"
   :interval 0.1 :max-tries 100))

(defun -aget-mailbox-status (mailbox)
  "Get the IMAP status of MAILBOX, as returned by the EXAMINE command."
  (athunk-let*
      ((cmd (format "EXAMINE %s" (-imap-quote (cdr mailbox))))
       (buffer <- (-amake-request (car mailbox) cmd)))
    (with-current-buffer buffer
      (-parse-select))))

(defun -afetch-id (mailbox uid)
  "Fetch the current ID of a message given its MAILBOX and UID."
  (athunk-let*
      ((buffer <- (-amake-request mailbox (format "UID FETCH %s (UID)" uid))))
    ;; NOTE: The command "FETCH * (UID)" is supposed to retrieve the
    ;; highest id, but servers seem to implement some kind of caching
    ;; that makes it not work.
    (with-current-buffer buffer
      (-message-id (car (-parse-fetch))))))

(defvar -message-cache nil)

(defvar -afetch-message-body nil
  "Synchronization data for the function of same name.")

(defun -afetch-message-body (mailbox uid)
  "Fetch body of message given its MAILBOX and UID, returning a string."
  (athunk-with-semaphore (alist-get (car mailbox) -afetch-message-body)
    (athunk-let*
        ((key (cons uid mailbox))
         (cached (assoc key -message-cache))
         (buffer <- (if cached
                        (athunk-wrap nil)
                      (-amake-request mailbox
                                      (format "UID FETCH %s (BODY[])" uid)))))
      (if cached
          (prog1 (cdr cached)
            (setq -message-cache (cons cached (delq cached -message-cache))))
        (with-current-buffer buffer
          (pcase-let* ((response (car (-parse-fetch)))
                       (`(,start . ,end) (alist-get 'content response))
                       (content (buffer-substring-no-properties start end)))
            (push (cons key content) -message-cache)
            (cl-callf2 ntake minimail-message-cache-size -message-cache)
            content))))
    :use-lifo-queue t))

(defun -afetch-message-info (mailbox set &optional brief sequential)
  "Fetch metadata for the given message SET in MAILBOX.

If BRIEF is non-nil, fetch flags but not envelope information.

If SEQUENTIAL is non-nil, SEQ is regarded as a set of sequential IDs
rather than UIDs."
  (athunk-let*
      ((caps <- (-aget-capability (car mailbox)))
       (cmd (format "%sFETCH %s (UID FLAGS%s%s%s)"
                    (if sequential "" "UID ")
                    (-format-sequence-set set)
                    (if (memq 'x-gm-ext-1 caps) " X-GM-LABELS" "")
                    (cond ((memq 'objectid caps) " THREADID")
                          ((memq 'x-gm-ext-1 caps) " X-GM-THRID")
                          (t ""))
                    (if brief "" " RFC822.SIZE ENVELOPE")))
       (buffer <- (-amake-request mailbox cmd)))
    (with-current-buffer buffer (-parse-fetch))))

(defun -afetch-old-messages (mailbox limit &optional before)
  "Fetch a message listing for MAILBOX with up to LIMIT elements.
If BEFORE is nil, retrieve the newest messages.  Otherwise, retrieve
messages with UID smaller than BEFORE."
  (athunk-let*
      ((end <- (if before
                   (-afetch-id mailbox before)
                 (athunk-let ((status <- (-aget-mailbox-status mailbox)))
                   (1+ (alist-get 'exists status)))))
       (start (max 1 (- end limit)))
       (messages <- (if (> end 1)
                        (-afetch-message-info mailbox
                                              `(range ,start ,(1- end))
                                              nil t)
                      (athunk-wrap nil))))
    messages))

(defun -afetch-new-messages (mailbox messages)
  "Return an updated message listing for MAILBOX.
MESSAGES is a list of message metadata alists.  Return a similar list
where new messages are added, deleted messages are removed and old
messages have their flags updated."
  (athunk-let*
      ((uidmin (seq-min (mapcar #'-message-uid messages)))
       (newflags <- (-afetch-message-info mailbox `(range ,uidmin t) t))
       ;; Forget about vanished messages and update flags of the rest
       (messages (let ((hash (make-hash-table)))
                   (dolist (msg newflags)
                     (puthash (-message-uid msg) msg hash))
                   (mapcan (lambda (msg)
                             (when-let* ((newmsg (gethash (-message-uid msg) hash)))
                               (list (-alist-merge newmsg msg))))
                           messages)))
       ;; Fetch new messages
       (newuids (let ((hash (make-hash-table)))
                  (dolist (msg messages)
                    (puthash (-message-uid msg) t hash))
                  (mapcan (lambda (msg)
                            (let ((uid (-message-uid msg)))
                              (unless (gethash uid hash)
                                (list uid))))
                          newflags)))
       (newmessages <- (if newuids
                           (-afetch-message-info mailbox newuids)
                         (athunk-wrap nil))))
    (nconc newmessages messages)))

(defun -afetch-search (mailbox query limit)
  "Search MAILBOX using QUERY string.
Return a list of up to LIMIT message metadata alists, as in
`minimail--afetch-message-info'."
  ;; TODO: add after argument, add UID 1:<after> arg
  (athunk-let*
      ((caps <- (-aget-capability (car mailbox)))
       (encoded (-imap-encode-command query))
       (charset (unless (eq query encoded)
                  (unless (seq-intersection '(literal+ literal-) caps)
                    (user-error
                     "Cannot use non-ASCII characters for search on this account"))
                  "CHARSET UTF-8 "))
       (cmd (concat "UID SEARCH " charset encoded))
       (buffer <- (-amake-request mailbox cmd))
       (set (with-current-buffer buffer (-parse-search)))
       (messages <- (-afetch-message-info mailbox (last set limit))))
    messages))

(defun -amove-messages (mailbox destination set)
  "Move message SET from MAILBOX to DESTINATION.
DESTINATION is just a string and refers to a mailbox in the same account
as the original MAILBOX."
  (athunk-let*
      ((caps <- (-aget-capability (car mailbox)))
       (cmd (if (memq 'move caps)
                (format "UID MOVE %s %s"
                        (-format-sequence-set set)
                        (-imap-quote destination))
              (error "Account %s doesn't support moving messages"
                     (car mailbox))))
       (_ <- (-amake-request mailbox cmd)))
    t))

(defun -astore-message-flags (mailbox set flags &optional remove)
  "Add FLAGS to each message in the MAILBOX message SET.
If REMOVE is non-nil, remove those flags instead.

If MAILBOX is displayed in some buffer, update it."
  (athunk-let*
      ((cmd (format "UID STORE %s %sFLAGS (%s)"
                    (-format-sequence-set set)
                    (if remove "-" "+")
                    (mapconcat (lambda (v) (if (symbolp v) (symbol-name v) v))
                               (ensure-list flags)
                               " ")))
       (buffer <- (-amake-request mailbox cmd))
       (result (with-current-buffer buffer (-parse-fetch))))
    ;; Possibly update displayed mailbox
    (dolist (buffer (buffer-list))
      (with-current-buffer buffer
        (when (and (equal -current-mailbox mailbox)
                   (derived-mode-p 'minimail-mailbox-mode))
          (dolist (msg -message-list)
            (when-let* ((uid (-message-uid msg))
                        (new (seq-find (lambda (it) (eq (-message-uid it) uid))
                                       result)))
              (setf (cdr (assq 'flags msg)) (-message-flags new))
              (ignore-errors
                (vtable-update-object (-vtable-ensure-table) msg)))))))
    result))

;;; Commands

(defun -find-buffer (type &optional noerror)
  "Return a TYPE buffer with same account and mailbox as the current ones.
TYPE can be `mailbox' or `message'.
If there is no such buffer and NOERROR is nil, signal an error."
  (let ((mailbox -current-mailbox)
        (mode (pcase-exhaustive type
                ('mailbox 'minimail-mailbox-mode)
                ('message 'minimail-message-mode))))
    (or (save-current-buffer
          (seq-find (lambda (buffer)
                      (set-buffer buffer)
                      (and (equal mailbox -current-mailbox)
                           (derived-mode-p mode)))
                    (buffer-list)))
        (unless noerror (user-error "No %s buffer" type)))))

(defun -mailbox-annotation (mbinfo)
  "Return an annotation for a mailbox given its metadata.
MBINFO can be an alist as returned by `minimail--aget-mailbox-listing'
or a string containing such an alist as a property."
  (let-alist (if (stringp mbinfo) (car (-get-data mbinfo)) mbinfo)
    (when .messages
      (let ((suffix (if (eq 1 .messages) "" "s")))
        (if (cl-plusp .unseen)
            (format " %s message%s, %s unseen" .messages suffix .unseen)
          (format " %s message%s" .messages suffix))))))

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
                     (annotation-function . -mailbox-annotation)))
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
                 ((mkcand (pcase-lambda (`(,mbname . ,props))
                            (unless (-key-match-p '(or \\Noselect \\NonExistent)
                                                  (alist-get 'flags props))
                              (propertize (-mailbox-display-name (cons acct mbname))
                                          'minimail `(,props ,acct . ,mbname)))))
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
  "Read a mailbox using PROMPT, unless a choice can be guessed from context."
  (or (get-text-property (point) '-current-mailbox)
      (when (cdr -current-mailbox) -current-mailbox)
      (-read-mailbox prompt (car -current-mailbox))))

(defun -current-message ()
  "Return the message object under point."
  (or (vtable-current-object) (user-error "No message under point")))

(defun -selected-messages ()
  "Return a list of message UIDs to act on.
Can be called in a mailbox or in a message buffer."
  (cond
   ((derived-mode-p 'minimail-message-mode)
    (list (alist-get 'uid -local-state)))
   ((derived-mode-p 'minimail-mailbox-mode)
    (if (use-region-p)
        ;; TODO: Ideally we would use a dired-style marking
        ;; mechanism, if vtable one day provides such a thing.
        (let (uids)
          (setq deactivate-mark t)
          (save-excursion
            (save-restriction
              (narrow-to-region (region-beginning) (region-end))
              (goto-char (point-min))
              (while (not (eobp))
                (push (-message-uid (vtable-current-object)) uids)
                (forward-line))))
          (or (nreverse (delq nil uids))
              (user-error "No message selected")))
      (list (-message-uid (-current-message)))))))

;;;###autoload
(defun minimail-find-mailbox (mailbox)
  "List messages in a mailbox.
MAILBOX is a cons cell of the account name as a symbol and mailbox name
as a string."
  (interactive (list (-read-mailbox "Find mailbox: ")))
  (pop-to-buffer
   (let* ((name (-mailbox-display-name mailbox))
          (buffer (get-buffer name)))
     (unless buffer
       (setq buffer (get-buffer-create name))
       (with-current-buffer buffer
         (minimail-mailbox-mode)
         (setq -current-mailbox mailbox)
         (-mailbox-buffer-populate)))
     buffer)))

;;;; Searching

(defclass -transient-search-option (transient-cons-option)
  ((format :initform " %k %d%v"))
  "Class for email search options.")

(cl-defmethod transient-format-value ((obj -transient-search-option))
  (if (not (oref obj value)) "" (concat ": " (cl-call-next-method))))

(defclass -transient-search-switch (-transient-search-option)
  ((choices :initform '(nil yes no)))
  "Class for email search switches.")

(cl-defmethod transient-infix-read ((obj -transient-search-switch))
  (cadr (member (oref obj value) (oref obj choices))))

(defun -format-search (items)
  (mapconcat
   (pcase-lambda (`(,key . ,value))
     (let ((tag (upcase (symbol-name key))))
       (pcase-exhaustive key
         ((or 'answered 'deleted 'flagged 'seen 'draft)
          (concat (pcase-exhaustive value ('yes nil) ('no "UN")) tag))
         ((or 'keyword 'larger 'smaller 'unkeyword) ;atom or number argument
          (format "%s %s" tag value))
         ((or 'bcc 'body 'cc 'from 'subject 'text 'to 'x-gm-raw) ;string argument
          (format "%s %S" tag value))
         ((or 'before 'on 'since 'sentbefore 'senton 'sentsince) ;date argument
          (pcase-let ((`(,day ,month ,year) (drop 3 (parse-time-string value))))
            (format "%s %s-%s-%s" tag day (aref -imap-months (1- month)) year)))
         ('raw (-get-data value)))))
   items " "))

(transient-define-prefix -search-transient ()
  "Transient menu for `minimail-search'."
  ["Email search"
   ("m" "Mailbox" :cons 'mailbox :class -transient-search-option
    :prompt "Search in mailbox: "
    :always-read t
    :reader
    (lambda (prompt _ _)
      (let ((mb (-read-mailbox prompt)))
        (propertize (-mailbox-display-name mb) 'minimail mb)))
    :init-value
    (lambda (obj)
      (let ((mb (-read-mailbox-maybe (transient-prompt obj))))
        (setf (oref obj value)
              (propertize (-mailbox-display-name mb) 'minimail mb)))))
   ("s" "Text (anywhere in message)" :cons 'text :class -transient-search-option
    :prompt "Messages containing: ")]
  [["Who"
    ("f" "From" :cons 'from :class -transient-search-option
     :prompt "Messages from: ")
    ("t" "To" :cons 'to :class -transient-search-option
     :prompt "Messages to: ")
    ("c" "CC"  :cons 'cc :class -transient-search-option
     :prompt "Messages with copy to: ")]
   ["When"
    ("d" "Date" :cons 'date :class -transient-search-option
     :prompt "Messages dated exactly: "
     :reader transient-read-date)
    ("<" "Before" :cons 'before :class -transient-search-option
     :prompt "Messages dated before: "
     :reader transient-read-date)
    (">" "Since" :cons 'since :class -transient-search-option
     :prompt "Messages dated after: "
     :reader transient-read-date)]
   ["What"
    ("u" "Subject" :cons 'subject :class -transient-search-option
     :prompt "Messages with subject containing: ")
    ("b" "Body" :cons 'body :class -transient-search-option
     :prompt "Messages with body containing: ")
    ("z" "Size" :cons 'raw :class -transient-search-option
     :prompt "\
Enter a number, optionally preceded by < or > and suffixed with a multiplier.
Messages with size (bytes): "
     :reader
     (lambda (prompt init hist)
       (let ((input (read-from-minibuffer prompt init nil nil hist)))
         (when (string-match (rx (group (? (any "<>"))) (? "=")
                                 (* space) (group (+ digit))
                                 (* space) (group (? (any "kKmM"))))
                             input)
           (let ((comp (pcase (match-string 1 input)
                         ("<" '("≤ " . "SMALLER %s"))
                         ((or ">" "") '("≥ " . "LARGER %s"))))
                 (n (* (string-to-number (match-string 2 input))
                       (pcase (downcase (match-string 3 input))
                         ("k" 1024) ("m" 1048576) (_ 1)))))
             (propertize (concat (car comp) (file-size-human-readable n))
                         'minimail (format (cdr comp) n)))))))]
   ["Flags"
    ("." "Seen" :cons 'seen :class -transient-search-switch)
    ("!" "Flagged" :cons 'flagged :class -transient-search-switch)
    ("a" "Answered" :cons 'answered :class -transient-search-switch)]]
  [[("RET" "Search"
     (lambda (arg)
       (interactive "P")
       (pcase-let* ((`((mailbox . ,mb) . ,items)
                     (transient-args transient-current-command))
                    (mailbox (or (-get-data mb) (error "No mailbox")))
                    (query (-format-search items)))
         (when arg
           (setq query (read-from-minibuffer "IMAP search: " query)))
         (minimail-search mailbox query))))]])
(put '-search-transient 'completion-predicate 'ignore)

(defun minimail-search (mailbox query)
  "Perform a search in a mailbox.
Search MAILBOX for QUERY and pop to the result buffer.

Interactively, or if QUERY is t, show a transient menu.  Else, QUERY
should be a string as in RFC 3501, § 6.4.4, except that quoted terms in
it may contain non-ASCII characters."
  (interactive '(nil t))
  (if (eq query t)
      (let ((-current-mailbox (or mailbox -current-mailbox)))
        (call-interactively #'-search-transient))
    (when (or (string-match-p (rx cntrl) query)
              (string-blank-p query))
      (user-error "Invalid search query"))
    (let* ((name (format "*search in %s*" (-mailbox-display-name mailbox)))
           (buffer (generate-new-buffer name)))
      (pop-to-buffer buffer)
      (minimail-mailbox-mode)
      (setq -current-mailbox mailbox)
      (setq -local-state `((search . ,query)))
      (-mailbox-buffer-populate)
      buffer)))

;;;; Moving

(defun -amove-messages-and-redisplay (mailbox destination set)
  "Move message SET from MAILBOX to DESTINATION.
This calls `minimail--amove-messages' and takes care of update the UI."
  (athunk-let*
      ((destname (-mailbox-display-name (cons (car mailbox) destination)))
       (prog (make-progress-reporter
              (format-message "Moving messages to `%s'..." destname)))
       (_ <- (-amove-messages mailbox destination set)))
    (progress-reporter-done prog)
    (when-let* ((-current-mailbox mailbox)
                (buffer (-find-buffer 'mailbox t)))
      (with-current-buffer buffer
        (let ((messages (seq-remove (lambda (msg)
                                      (memq (-message-uid msg) set))
                                    -message-list))
              (showing (when-let* ((msgbuf (-find-buffer 'message t)))
                         (get-buffer-window msgbuf)))
              (next (-vtable-find-object
                     (lambda (m) (not (memq (-message-uid m) set)))
                     t)))
          (-mailbox-buffer-update messages)
          (unless next
            ;; Above, we tried to move point to the next message not
            ;; to be removed.  If not found, then go to the last
            ;; remaining message.
            (vtable-end-of-table)
            (forward-line -1))
          (when (and showing (not overlay-arrow-position))
            ;; If we were displaying a message and now it's gone,
            ;; display message under point.
            (minimail-show-message)))))))

(defun minimail-move-to-mailbox (&optional destination)
  "Move messages to a given DESTINATION mailbox.
In a mailbox buffer, act on the message under point or, if the region is
active, all messages in the region.  In a message buffer, act on the
current message."
  (interactive nil minimail-mailbox-mode minimail-message-mode)
  (let* ((mailbox -current-mailbox)
         (uids (-selected-messages))
         (prompt (if (length= uids 1)
                     "Move message to: "
                   (format "Move %s messages to: " (length uids))))
         (dest (or destination
                   (cdr (-read-mailbox prompt (car mailbox))))))
    (athunk-run
     (-amove-messages-and-redisplay mailbox dest uids))))

(defun -find-mailbox-by-flag (flag mailboxes)
  "Return the first item of MAILBOXES which has the given FLAG.
FLAG can be a string or, more generally, a condition for
`minimail--key-match-p'."
  (seq-some (pcase-lambda (`(,mailbox . ,items))
              (when (-key-match-p flag (alist-get 'flags items)) mailbox))
            mailboxes))

(defun minimail-move-to-archive ()
  "Move messages to the archive mailbox.
In a mailbox buffer, act on the message under point or, if the region is
active, all messages in the region.  In a message buffer, act on the
current message."
  (interactive nil minimail-mailbox-mode minimail-message-mode)
  (let ((mailbox -current-mailbox)
        (uids (-selected-messages)))
    (athunk-run
     (athunk-let*
         ((mailboxes <- (-aget-mailbox-listing (car mailbox)))
          (dest (or (plist-get (alist-get (car mailbox) minimail-accounts)
                               :archive-mailbox)
                    (-find-mailbox-by-flag '\\Archive mailboxes)
                    (-find-mailbox-by-flag '\\All mailboxes)
                    (user-error "Archive mailbox not found")))
          (_ <- (-amove-messages-and-redisplay mailbox dest uids)))))))

(defun minimail-move-to-trash ()
  "Move messages to the trash mailbox.
In a mailbox buffer, act on the message under point or, if the region is
active, all messages in the region.  In a message buffer, act on the
current message."
  (interactive nil minimail-mailbox-mode minimail-message-mode)
  (let ((mailbox -current-mailbox)
        (uids (-selected-messages)))
    (athunk-run
     (athunk-let*
         ((mailboxes <- (-aget-mailbox-listing (car mailbox)))
          (dest (or (plist-get (alist-get (car mailbox) minimail-accounts)
                               :trash-mailbox)
                    (-find-mailbox-by-flag '\\Trash mailboxes)
                    (user-error "Trash mailbox not found")))
          (_ <- (-amove-messages-and-redisplay mailbox dest uids)))))))

(defun minimail-move-to-junk ()
  "Move messages to the junk mailbox.
In a mailbox buffer, act on the message under point or, if the region is
active, all messages in the region.  In a message buffer, act on the
current message."
  (interactive nil minimail-mailbox-mode minimail-message-mode)
  (let ((mailbox -current-mailbox)
        (uids (-selected-messages)))
    (athunk-run
     (athunk-let*
         ((mailboxes <- (-aget-mailbox-listing (car mailbox)))
          (dest (or (plist-get (alist-get (car mailbox) minimail-accounts)
                               :junk-mailbox)
                    (-find-mailbox-by-flag '\\Junk mailboxes)
                    (user-error "Junk mailbox not found")))
          (_ <- (-amove-messages-and-redisplay mailbox dest uids)))))))

(defun minimail-execute-server-command (mailbox command)
  "Execute an IMAP COMMAND in MAILBOX for debugging purposes."
  (interactive (let ((mailbox (-read-mailbox-maybe "IMAP command in: ")))
                 (list mailbox
                       (read-from-minibuffer
                        (format-prompt "IMAP command in %s" nil
                                       (-mailbox-display-name mailbox))))))
  (pcase-let ((`(,status ,message)
               (athunk-run-polling
                (athunk-condition-case v
                    (-amake-request mailbox command)
                  (:success `(ok ,(with-current-buffer v (buffer-string))))
                  (-imap-error (cdr v)))
                :message "Contacting IMAP server"
                :interval 0.1 :max-tries 100)))
    (prog1 status (princ message))))

;;; Mailbox buffer

(defvar-local -thread-data nil)
(defvar-local -sort-by-thread nil)

(defvar-keymap minimail-base-keymap
  :doc "Common keymap for Minimail mailbox and message buffers."
  "n" #'minimail-next-message
  "p" #'minimail-previous-message
  "r" #'minimail-reply
  "R" #'minimail-reply-all
  "f" #'minimail-forward
  "s" #'minimail-search
  "A" #'minimail-move-to-archive
  "J" #'minimail-move-to-junk
  "D" #'minimail-move-to-trash
  "M" #'minimail-move-to-mailbox
  "SPC" #'minimail-message-scroll-up
  "S-SPC" #'minimail-message-scroll-down
  "DEL" #'minimail-message-scroll-down)

(defvar-keymap minimail-mailbox-mode-map
  :parent (make-composed-keymap (list minimail-base-keymap vtable-map)
                                special-mode-map)
  "RET" #'minimail-show-message
  "+" #'minimail-load-more-messages
  "=" #'minimail-quit-message-window
  "T" #'minimail-toggle-sort-by-thread
  "g" #'revert-buffer)

(define-derived-mode minimail-mailbox-mode special-mode "Mailbox"
  "Major mode for mailbox listings."
  :interactive nil
  (add-hook 'quit-window-hook #'minimail-quit-message-window nil t)
  ;; Ensure we preserve sorting by column in the following sequence of
  ;; steps: sort by thread, then sort by column, then refresh buffer.
  (add-hook '-vtable-before-sort-by-current-column-hook
            (lambda () (setq -sort-by-thread nil))
            nil t)
  (setq-local
   buffer-undo-list t
   revert-buffer-function #'-mailbox-buffer-refresh
   truncate-lines t))

(defun -base-subject (string)
  "Simplify message subject STRING for sorting and threading purposes."
  (let ((case-fold-search t))
    (replace-regexp-in-string message-subject-re-regexp ""
                              (downcase (or string "")))))

(defun -format-subject (message)
  "Subject string of MESSAGE formatted for the mailbox buffer."
  (let* ((ancestors (when -sort-by-thread
                      (reverse (-thread-ancestors message)))))
    (concat
     ;; Indicate an incomplete thread
     (when (alist-get 'in-reply-to (-message-envelope (car ancestors)))
       (when (eq (car ancestors) message)
         (icon-string 'minimail-thread-false-root)))
     ;; Thread tree prefix
     (mapconcat
      (lambda (msg)
        (icon-string
         (let ((siblings (-thread-children (-thread-parent msg))))
           (if (cdr (memq msg siblings)) ;not the last among its siblings
               (if (eq msg message)
                   'minimail-thread-leaf-nonterminal
                 'minimail-thread-parent-nonterminal)
             (if (eq msg message)
                 'minimail-thread-leaf-terminal
               'minimail-thread-parent-terminal)))))
      (cdr ancestors))
     ;; The subject itself, possibly mangled
     (let* ((subject (or (-message-subject message) ""))
            (boring (-base-subject (-message-subject (-thread-parent message))))
            (shortened (when (and (not (string-blank-p boring))
                                  (string-suffix-p boring subject t))
                         (substring subject 0 (- (length boring)))))
            (flags (-message-flags message)))
       (propertize (if shortened
                       (concat shortened (truncate-string-ellipsis))
                     subject)
                   'face (-alist-query flags minimail-subject-faces))))))

(defun -format-names (addresses)
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

(defun -format-date (date)
  (let* ((current-time-list nil)
         (timestamp (condition-case nil (encode-time date) (t 0)))
         (today (let ((v (decode-time)))
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
                  (format-time-string "%a, %d %b %Y %T" timestamp)))))

(defun -message-timestamp (message)
  "The MESSAGE envelope date as a Unix timestamp."
    (let ((current-time-list nil))
      (condition-case nil
          (encode-time (alist-get 'date (-message-envelope message)))
        (t 0))))

(defvar minimail-mailbox-mode-column-alist
  ;; NOTE: We must slightly abuse the vtable API in several of our
  ;; column definitions.  The :getter attribute returns a string used
  ;; as sort key while :formatter fetches from it the actual display
  ;; string, embedded as a string property.
  `((id
     :name "#"
     :getter -message-id)
    (flag-seen
     :name "Seen"
     :min-width 1
     :getter ,(lambda (msg _)
                (let ((icon (-alist-query
                             (-message-flags msg)
                             '(((not \\Seen) . minimail-message-unseen)))))
                  (if icon (icon-string icon) ""))))
    (flag-flagged
     :name "Flagged"
     :min-width 1
     :getter
     ,(lambda (msg _)
        (let ((icon (-alist-query
                     (append (alist-get 'x-gm-labels msg)
                             (-message-flags msg))
                     '((\\Flagged                   . minimail-message-flagged)
                       ((or $Important \\Important) . minimail-message-important)
                       ($Phishing                   . minimail-message-phishing)
                       ($Junk                       . minimail-message-junk)))))
          (if icon (icon-string icon) ""))))
    (flag-answered
     :name "Answered"
     :min-width 1
     :getter ,(lambda (msg _)
                (let ((icon (-alist-query
                             (-message-flags msg)
                             '((\\Answered . minimail-message-answered)
                               ($Forwarded . minimail-message-forwarded)))))
                  (if icon (icon-string icon) ""))))
    (from
     :name "From"
     :max-width 30
     :getter ,(lambda (msg _)
                (-format-names (alist-get 'from (-message-envelope msg)))))
    (to
     :name "To"
     :max-width 30
     :getter ,(lambda (msg _)
                (-format-names (alist-get 'to (-message-envelope msg)))))
    (recipients
     :name "Recipients"
     :max-width 30
     :getter ,(lambda (msg _)
                (let-alist (-message-envelope msg)
                  (-format-names (append .to .cc .bcc)))))
    (subject
     :name "Subject"
     :max-width 80
     :getter ,(lambda (msg _)
                (let ((s (-base-subject (-message-subject msg))))
                  (propertize (if (string-empty-p s) "\0" s)
                              'minimail msg)))
     :formatter ,(lambda (s) (-format-subject (-get-data s))))
    (date
     :name "Date"
     :width 12
     :getter ,(lambda (msg _)
                ;; The envelope date as Unix timestamp, formatted as a
                ;; hex string.  This ensures the correct sorting.
                (propertize (format "%09x" (-message-timestamp msg))
                            'minimail (alist-get 'date (-message-envelope msg))))
     :formatter ,(lambda (s)
                   (propertize (-format-date (-get-data s))
                               'face 'vtable)))
    (size
     :name "Size"
     :getter ,(lambda (msg _) (alist-get 'rfc822-size msg))
     :formatter ,(lambda (v)
                   (propertize (file-size-human-readable-iec v)
                               'face 'vtable)))))

(defun -mailbox-buffer-update (messages)
  "Set `minimail--message-list' to MESSAGES and do all necessary adjustments."
  (-vtable-ensure-table)
  (setq -message-list messages)
  (setq -thread-data nil)
  (let ((point-uid (-message-uid (vtable-current-object)))
        (arrow-uid (when overlay-arrow-position
                     (save-excursion
                       (goto-char overlay-arrow-position)
                       (-message-uid (vtable-current-object))))))
    (vtable-revert-command)
    (when -sort-by-thread
      ;; FIXME: Can we avoid drawing the table twice?
      (-sort-by-thread (eq -sort-by-thread 'descend)))
    (when arrow-uid
      (save-excursion
        (if (-vtable-find-object (lambda (m) (eq (-message-uid m)
                                                 arrow-uid)))
            (move-marker overlay-arrow-position (point))
          (setq overlay-arrow-position nil))))
    (-vtable-find-object (lambda (m) (eq (-message-uid m) point-uid))))
  (save-excursion
    (let* ((inhibit-read-only t)
           (count (length messages))
           (idmax (seq-reduce (lambda (i msg) (max i (-message-id msg)))
                              messages 0)))
      (vtable-end-of-table)
      (delete-region (point) (point-max))
      (insert (if (eq count idmax)
                  "Showing all messages\n"
                (format "Showing %s of %s messages %s\n" count idmax
                        (buttonize "[load more]"
                                   (lambda (_)
                                     (minimail-load-more-messages)))))))))

(defun -mailbox-buffer-populate (&rest _)
  "Fetch messages for the first time and create a vtable in the current buffer."
  (let* ((buffer (current-buffer))
         (mailbox -current-mailbox)
         (limit (-settings-scalar-get :fetch-limit mailbox))
         (search (alist-get 'search -local-state)))
    (-set-mode-line-suffix 'loading)
    (athunk-run
     (athunk-let*
         ((messages <- (athunk-condition-case err
                           (if search
                               (-afetch-search mailbox search limit)
                             (-afetch-old-messages mailbox limit))
                         (t (with-current-buffer buffer
                              (-set-mode-line-suffix err))
                            (signal (car err) (cdr err))))))
       (with-current-buffer buffer
         (-set-mode-line-suffix nil)
         (let* ((inhibit-read-only t)
                (vtable-map (make-sparse-keymap)) ;only way to disable extra keymap
                (colnames (-settings-alist-get :mailbox-columns mailbox))
                (sortnames (-settings-alist-get :mailbox-sort-by mailbox)))
           (make-vtable
            :objects-function (lambda () (or -message-list '(((uid . 0)))))
            :columns (mapcar (lambda (v)
                               (alist-get v minimail-mailbox-mode-column-alist))
                             colnames)
            :sort-by (mapcan (pcase-lambda (`(,col . ,dir))
                               (when-let* ((i (seq-position colnames col)))
                                 `((,i . ,dir))))
                             sortnames))
           (setq -sort-by-thread (alist-get 'thread sortnames)))
         (-mailbox-buffer-update messages))))))

(defun -mailbox-buffer-refresh (&rest _)
  (unless (derived-mode-p #'minimail-mailbox-mode)
    (user-error "This should be called only from a mailbox buffer."))
  (let* ((buffer (current-buffer))
         (mailbox -current-mailbox)
         (messages -message-list)
         (search (alist-get 'search -local-state)))
    (when search (error "Not implemented"))
    (-set-mode-line-suffix 'loading)
    (athunk-run
     (athunk-let*
         ((messages <- (athunk-condition-case err
                           (-afetch-new-messages mailbox messages)
                         (t (with-current-buffer buffer
                              (-set-mode-line-suffix err))
                            (signal (car err) (cdr err))))))
       (with-current-buffer buffer
         (-set-mode-line-suffix nil)
         (-mailbox-buffer-update messages))))))

(defun minimail-load-more-messages (&optional count)
  "Add older messages to the current mailbox buffer.
With a prefix argument (or COUNT argument from Lisp), load up to that
many message, otherwise use `minimail-fetch-limit'."
  (interactive (list (when current-prefix-arg
                       (prefix-numeric-value current-prefix-arg)))
               minimail-mailbox-mode)
  (let* ((buffer (current-buffer))
         (mailbox -current-mailbox)
         (messages -message-list)
         (search (alist-get 'search -local-state))
         (limit (or count (-settings-scalar-get :fetch-limit mailbox)))
         (before (seq-min (mapcar (lambda (msg) (-message-uid msg)) messages))))
    (when search (error "Not implemented"))
    (-set-mode-line-suffix 'loading)
    (athunk-run
     (athunk-let*
         ((old <- (athunk-condition-case err
                      (-afetch-old-messages mailbox limit before)
                    (t (with-current-buffer buffer
                         (-set-mode-line-suffix err))
                       (signal (car err) (cdr err))))))
       (with-current-buffer buffer
         (-set-mode-line-suffix nil)
         (unless old (user-error "No more old messages"))
         (-mailbox-buffer-update (nconc old messages)))))))

(defun minimail-show-message ()
  (interactive nil minimail-mailbox-mode)
  (let ((msg (-current-message)))
    (unless (member "\\Seen" (-message-flags msg))
      (push "\\Seen" (cdr (assq 'flags msg)))
      (vtable-update-object (vtable-current-table) msg))
    (setq-local overlay-arrow-position (copy-marker (pos-bol)))
    (athunk-run (-adisplay-message -current-mailbox (-message-uid msg)))))

(defun minimail-show-message-raw ()
  (interactive nil minimail-mailbox-mode)
  (let ((-message-rendering-function #'ignore))
    (minimail-show-message)))

(defun minimail-next-message (count)
  (interactive "p" minimail-mailbox-mode minimail-message-mode)
  (with-current-buffer (-find-buffer 'mailbox)
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

(defun minimail-quit-message-window (&optional kill)
  "If there is a window showing a message from this mailbox, quit it.
If KILL is non-nil, kill the message buffer instead of burying it."
  (interactive nil minimail-mailbox-mode)
  (when-let* ((msgbuf (-find-buffer 'message t))
              (window (get-buffer-window msgbuf)))
    (quit-restore-window window (if kill 'kill 'bury))))

;;;; Sorting by thread

(defun -thread-data-shallow (messages)
  "Compute a shallow message thread tree from MESSAGES.
Use server-side thread identifiers if available, otherwise infer the
thread structure from the message subjects."
  (let* ((result (make-hash-table))
         (threads (make-hash-table :test #'equal)))
    (dolist (msg messages)
      (push msg (gethash (or (alist-get 'thread-id msg)
                             (-base-subject (-message-subject msg)))
                         threads)))
    (dolist (thread (hash-table-values threads))
      (cl-callf sort thread :key #'-message-timestamp :in-place t)
      (setf (alist-get 'children (gethash (car thread) result)) (cdr thread))
      (dolist (child (cdr thread))
        (setf (alist-get 'parent (gethash child result)) (car thread))))
    result))

(defun -thread-data-hierarchical (messages)
  "Compute a hierarchical message thread tree from MESSAGES.
This relies solely on Message-ID and In-Reply-To headers from the IMAP
envelope and doesn't use server-side threading information."
  (let* ((result (make-hash-table))
         (msgids (make-hash-table :test #'equal))) ;map Message-ID -> msg
    (dolist (msg messages)
      (when-let* ((msgid (alist-get 'message-id (-message-envelope msg))))
        (puthash msgid msg msgids)))
    (dolist (msg messages)
      (when-let*
          ((inreply (alist-get 'in-reply-to (-message-envelope msg)))
           (inreply (when (string-match "<.*?>" inreply)
                      (match-string-no-properties 0 inreply)))
           (parent (gethash inreply msgids)))
        (setf (alist-get 'parent (gethash msg result)) parent)
        (push msg (alist-get 'children (gethash parent result)))))
    (dolist (msg messages)
      (cl-callf sort (alist-get 'children (gethash msg result))
        :key #'-message-timestamp
        :in-place t))
    result))

(defun -thread-data ()
  (with-memoization -thread-data
    (funcall (pcase-exhaustive
                 (-settings-scalar-get :thread-style -current-mailbox)
               ('shallow #'-thread-data-shallow)
               ('hierarchical #'-thread-data-hierarchical)
               ('nil (lambda (_) (make-hash-table))))
             -message-list)))

(defun -thread-parent (message)
  "The parent of MESSAGE in the thread tree."
  (alist-get 'parent (gethash message (-thread-data))))

(defun -thread-children (message)
  "All immediate children of MESSAGE in the thread tree."
  (alist-get 'children (gethash message (-thread-data))))

(defun -thread-ancestors (message)
  "All ancestors of MESSAGE, from itself up until the thread root."
  (with-memoization (alist-get 'ancestors (gethash message (-thread-data)))
    (let ((parent (-thread-parent message)))
      (cons message (when parent (-thread-ancestors parent))))))

(defun -thread-flat (message)
  "The subthread headed by MESSAGE, as a flat list."
  (with-memoization (alist-get 'flat (gethash message (-thread-data)))
    (cons message (seq-mapcat #'-thread-flat (-thread-children message)))))

(defun -thread-position (message)
  "The position of MESSAGE within its thread."
  (let ((root (car (last (-thread-ancestors message)))))
    (seq-position (-thread-flat root) message #'eq)))

(defun -sort-by-thread (&optional descend)
  "Sort messages with grouping by threads.

Within a thread, sort each message after its parents.  Across threads,
preserve the existing order, in the sense that thread A sorts before
thread B if some message from A comes before all messages of B.  This
makes sense when the current sort order is in the “most relevant at top”
style.  If DESCEND is non-nil, use the opposite convention."
  (let* ((table (-vtable-ensure-table))
         (rootpos (make-hash-table))
         (key (lambda (msg)
                (let ((root (car (last (-thread-ancestors msg)))))
                  (cons (gethash root rootpos) (-thread-position msg)))))
         (i 0)
         messages)
    (save-excursion
      ;; Get messages in current sort order (unlike `vtable-objects')
      ;; and at the same time fill rootpos with the sorting position
      ;; of each thread root.
      (vtable-beginning-of-table)
      (while-let ((msg (vtable-current-object)))
        (let* ((root (car (last (-thread-ancestors msg))))
               (j (gethash root rootpos))
               (k (cond ((not j) i)
                        (descend (max i j))
                        (t (min i j)))))
          (puthash root k rootpos))
        (push msg messages)
        (cl-incf i)
        (forward-line)))
    (setq -message-list (sort messages :key key :in-place t))
    ;; Little hack to force vtable to redisplay with our new sorting.
    (cl-letf (((vtable-sort-by table) nil))
      (vtable-revert-command))))

(defun minimail-toggle-sort-by-thread ()
  "Toggle sorting messages by thread."
  (interactive nil minimail-mailbox-mode)
  (setq -sort-by-thread (cadr (memq -sort-by-thread '(nil ascend descend))))
  (message "Sorting by thread: %s" (or -sort-by-thread "disabled"))
  ;; First re-sort the table by the original criteria, either
  ;; because that's the final goal (new is nil) or in preparation
  ;; for the thread sorting step.
  (vtable-revert-command)
  (when -sort-by-thread
    (-sort-by-thread (eq -sort-by-thread 'descend))))

;;; Message buffer

(defvar -message-erase-function #'erase-buffer
  "Function called to erase a message buffer.")

(defvar-keymap minimail-message-mode-map
  :parent (make-composed-keymap (list minimail-base-keymap button-buffer-map)
                                special-mode-map))

(define-derived-mode minimail-message-mode special-mode "Message"
  "Major mode for email messages."
  :interactive nil
  (setq buffer-undo-list t))

(defun -message-buffer-name (mailbox uid)
  "Name of buffer to display MAILBOX message with given UID."
  (format "%s[%s]" (-mailbox-display-name mailbox) uid))

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

(defun -adisplay-message (mailbox uid)
  "Display the message identified by MAILBOX and UID.
Return an athunk which yields the buffer displaying the message.
If the operation of displaying the message is canceled, say because
the user selected another message in the meanwhile, yield nil."
  (let ((render -message-rendering-function)
        (buffer (or (-find-buffer 'message t)
                    (generate-new-buffer
                     (-message-buffer-name mailbox "")))))
    (with-current-buffer buffer
      (unless (derived-mode-p #'minimail-message-mode)
        (minimail-message-mode))
      (-set-mode-line-suffix 'loading)
      (setf (alist-get 'next-message -local-state)
            (list mailbox uid)))
    (display-buffer buffer -display-message-base-action)
    (athunk-let*
        ((text <- (athunk-condition-case err
                      (-afetch-message-body mailbox uid)
                    (t (with-current-buffer buffer
                         (-set-mode-line-suffix err))
                       (signal (car err) (cdr err))))))
      (when (buffer-live-p buffer)
        (with-current-buffer buffer
          (when (equal (alist-get 'next-message -local-state)
                       (list mailbox uid))
            (let ((inhibit-read-only t))
              (-set-mode-line-suffix nil)
              (funcall -message-erase-function)
              (setq -current-mailbox mailbox)
              (setf (alist-get 'uid -local-state) uid)
              (rename-buffer (-message-buffer-name mailbox uid) t)
              (decode-coding-string text 'raw-text-dos nil buffer)
              (setf (alist-get 'headers -local-state)
                    (save-restriction
                      (message-narrow-to-headers-or-head)
                      (mapcan
                       (lambda (k)
                         (when-let* ((v (message-fetch-field (symbol-name k))))
                           `((,k . ,(mail-decode-encoded-word-string v)))))
                       '( from to cc subject date message-id references
                          ;; Funny stuff used to compute the
                          ;; recipients of a reply:
                          mail-copies-to mail-followup-to mail-reply-to
                          original-to reply-to))))
              (funcall render)
              (set-buffer-modified-p nil)
              (when-let* ((window (get-buffer-window (current-buffer))))
                (set-window-point window (point-min)))
              buffer)))))))

(defun minimail-message-scroll-up (arg &optional reverse)
  (interactive "^P" minimail-message-mode minimail-mailbox-mode)
  (with-current-buffer (-find-buffer 'message)
    (condition-case nil
        (if-let* ((window (get-buffer-window)))
            (with-selected-window window
              (funcall (if reverse #'scroll-down-command #'scroll-up-command)
                       arg))
          (display-buffer (current-buffer) -display-message-base-action))
      (beginning-of-buffer (with-current-buffer (-find-buffer 'mailbox)
                             (minimail-next-message -1)))
      (end-of-buffer (with-current-buffer (-find-buffer 'mailbox)
                       (minimail-next-message 1))))))

(defun minimail-message-scroll-down (arg)
  (interactive "^P" minimail-message-mode minimail-mailbox-mode)
  (minimail-message-scroll-up arg t))

(defun -reply-recipients (headers wide)
  "Compute recipients of a reply from the original message HEADERS."
  ;; We really want to reuse the rather complex logic of
  ;; `message-get-reply-headers' which, sadly, reads headers from the
  ;; current buffer.  At the same time, we want to honor buffer-local
  ;; values of variables such as `user-mail-address'.  So use the
  ;; current buffer (a message buffer) as scratch area.
  (save-restriction
    (widen)
    (goto-char (point-min))
    (pcase-dolist (`(,key . ,value) headers)
      (when value
        (insert (symbol-name key) ": " value ?\n)))
    (insert ?\n)
    (let ((end (point-marker)))
      (prog1
          (or (funcall (if wide
                           message-wide-reply-to-function
                         message-reply-to-function))
              (message-get-reply-headers wide))
        (delete-region (point-min) end)))))

(defun minimail-reply (&optional cite wide)
  (interactive (list (xor current-prefix-arg minimail-reply-cite-original))
               minimail-message-mode
               minimail-mailbox-mode)
  (athunk-run
   (athunk-let*
       ((buffer <- (if (derived-mode-p 'minimail-message-mode)
                       (athunk-wrap (current-buffer))
                     (-adisplay-message -current-mailbox
                                        (-message-uid (-current-message))))))
     (set-buffer (or buffer (user-error "No message buffer")))
     (let ((mailbox -current-mailbox)
           (uid (alist-get 'uid -local-state))
           (headers (alist-get 'headers -local-state)))
       (-compose-mail                   ;this changes current buffer
        nil nil nil nil nil buffer
        `((funcall ,(lambda ()
                        (athunk-run
                         (-astore-message-flags mailbox uid '\\Answered))))))
       (pcase-dolist (`(,key . ,value) (-reply-recipients headers wide))
         (message-replace-header (symbol-name key) value))
       (let-alist headers
         (message-replace-header
          "Subject" (concat "Re: " (message-simplify-subject .subject)))
         (message-replace-header
          "In-Reply-To" .message-id)
         (message-replace-header
          "References" (concat .references (when .references " ") .message-id)))
       (message-sort-headers)
       (message-hide-headers)
       (setq buffer-undo-list nil)
       (message-goto-body)
       (when cite
         (with-undo-amalgamate
           (message-yank-original)))))))

(defun minimail-reply-all (cite)
  (interactive (list (xor current-prefix-arg minimail-reply-cite-original))
               minimail-message-mode
               minimail-mailbox-mode)
  (minimail-reply cite t))

(defun minimail-forward ()
  (interactive nil minimail-message-mode minimail-mailbox-mode)
  (athunk-run
   (athunk-let*
       ((buffer <- (if (derived-mode-p 'minimail-message-mode)
                       (athunk-wrap (current-buffer))
                     (-adisplay-message -current-mailbox
                                        (-message-uid (-current-message))))))
     (set-buffer (or buffer (user-error "No message buffer")))
     (let* ((mailbox -current-mailbox)
            (uid (alist-get 'uid -local-state))
            (message-forward-decoded-p t)
            (subject (message-make-forward-subject)))
       (-compose-mail                   ;this changes current buffer
        nil subject nil nil nil nil
        `((funcall ,(lambda ()
                        (athunk-run
                         (-astore-message-flags mailbox uid '$Forwarded))))))
       (message-forward-make-body buffer)))))

;;;; Gnus graft
;; Cf. `mu4e--view-render-buffer' from mu4e-view.el

(defun -gnus-render-message ()
  "Render message in the current buffer using the Gnus machinery."
  (add-hook 'kill-buffer-hook
            (lambda () (mm-destroy-parts gnus-article-mime-handles))
            nil t)
  (add-function :before (local '-message-erase-function)
                (lambda ()
                  (mm-destroy-parts gnus-article-mime-handles)
                  (dolist (ov (overlays-in (point-min) (point-max)))
                    (delete-overlay ov))))
  ;; Gnus has the curious habit of not declaring its buffer-local
  ;; variables as such, so we need to take care to include all
  ;; relevant variables here.
  (setq-local
   gnus-article-buffer (current-buffer)
   gnus-article-charset nil
   gnus-article-current nil
   gnus-article-current-summary nil
   gnus-article-decoded-p nil
   gnus-article-ignored-charsets nil
   gnus-article-image-alist nil
   gnus-article-mime-handle-alist nil
   gnus-article-mime-handles nil
   gnus-article-wash-types nil
   gnus-blocked-images ""               ;FIXME: make customizable
   gnus-header-button-alist nil         ;FIXME: make customizable
   gnus-button-alist nil                ;FIXME: make customizable
   gnus-newsgroup-charset nil
   gnus-newsgroup-name nil
   gnus-summary-buffer nil
   nobreak-char-display nil)
  (run-hooks 'gnus-article-decode-hook)
  (setq gnus-article-decoded-p gnus-article-decode-hook)
  (gnus-display-mime)
  (when gnus-mime-display-attachment-buttons-in-header
    (gnus-mime-buttonize-attachments-in-header)))

(advice-add #'gnus-article-check-buffer :before-until
            (lambda () (derived-mode-p #'minimail-message-mode))
            '((name . minimail)))

;;; Overview buffer

(defvar-local -tree-widgets nil)

(defvar-keymap minimail-overview-mode-map
  :parent (make-composed-keymap widget-keymap special-mode-map)
  ":" #'minimail-execute-server-command
  "m" #'compose-mail
  "s" #'minimail-search)

(define-derived-mode minimail-overview-mode special-mode "Minimail"
  "Major mode for browsing a mailbox tree."
  :interactive nil
  (setq buffer-undo-list t)
  (add-hook 'tree-widget-before-create-icon-functions #'-overview-create-icon nil t)
  (setq-local revert-buffer-function (lambda (&rest _)
                                       (-overview-buffer-populate t))))

(defun -overview-create-icon (icon)
  (widget-put icon :glyph-name nil)
  (widget-put icon :tag
              (icon-string
               (pcase (widget-type icon)
                 ('tree-widget-leaf-icon
                  (widget-put icon :tab-order -1)
                  (widget-get (widget-get icon :node) :icon))
                 ('tree-widget-open-icon 'minimail-mailbox-open)
                 (_ 'minimail-mailbox-closed)))))

(defun -overview-tree-expand (widget)
  (let ((acct (widget-get widget :account))
        (path (widget-get widget :path)))
    (mapcan
     (pcase-lambda (`(,name . ,props))
       (let-alist props
         (when (equal path (cdr .path))
           (let ((node (if (-key-match-p '(or \\Noselect \\NonExistent) .flags)
                           `(item :tag ,(car .path))
                         `(link
                           :tag ,(propertize (car .path)
                                             '-current-mailbox (cons acct name))
                           :format "%[%t%]%d"
                           :button-prefix ""
                           :button-suffix ""
                           :doc ,(propertize (or (-mailbox-annotation props) "")
                                             'face 'completions-annotations)
                           :icon
                           ,(seq-some
                             (pcase-lambda (`(,cond . ,icon))
                               (when (-key-match-p cond .flags) icon))
                             '(((or \\All \\Archive) . minimail-mailbox-archive)
                               (\\Drafts             . minimail-mailbox-drafts)
                               (\\Flagged            . minimail-mailbox-flagged)
                               (\\Important          . minimail-mailbox-important)
                               (\\Junk               . minimail-mailbox-junk)
                               (\\Sent               . minimail-mailbox-sent)
                               (\\Trash              . minimail-mailbox-trash)
                               (t                    . minimail-mailbox)))
                           :action
                           ,(lambda (&rest _)
                              (minimail-find-mailbox
                               (get-text-property (point) '-current-mailbox)))))))
             (if (-key-match-p '(or \\HasNoChildren \\Noinferiors) .flags)
                 `(,node)
               `((tree-widget :node ,node
                              :account ,acct
                              :path ,.path
                              :expander -overview-tree-expand)))))))
     (widget-get (alist-get acct -tree-widgets) :mailboxes))))

(defun -overview-buffer-populate (&optional refresh)
  "Insert mailbox tree widgets to the current buffer.
Unless REFRESH is non-nil, use cached mailbox information."
  (let ((inhibit-read-only t)
        (buffer (current-buffer))
        (accounts (or (mapcar #'car minimail-accounts)
                      (user-error "No accounts configured"))))
    (-set-mode-line-suffix 'loading)
    (when (and (bolp) (eolp))
      (dolist (acct accounts)
        (setf (alist-get acct -tree-widgets)
              (widget-create 'tree-widget
                             :tag (symbol-name acct)
                             :account acct
                             :path nil
                             :open t
                             :expander-p #'always ;don't cache children
                             :expander #'-overview-tree-expand)))
      (goto-char (point-min)))
    (dolist (acct accounts)
      (athunk-run
       (athunk-let*
           ((mailboxes <- (athunk-condition-case err
                              (-aget-mailbox-listing acct refresh)
                            (t (-set-mode-line-suffix err)
                               (signal (car err) (cdr err)))))
            ;; Add path property to the mailbox items.
            (props (alist-get acct minimail-accounts))
            (url (url-generic-parse-url (plist-get props :incoming-url)))
            (basepath (string-remove-prefix "/" (car (url-path-and-query url))))
            (mailboxes (mapcar
                        (pcase-lambda (`(,name . ,props))
                          (let* ((delim (alist-get 'delimiter props))
                                 (path (nreverse
                                        (append
                                         (unless (string-empty-p basepath)
                                           (list basepath))
                                         (split-string
                                          (string-remove-prefix basepath name)
                                          (regexp-quote delim) t)))))
                            `(,name (path . ,path) ,@props)))
                        mailboxes)))
         (with-current-buffer buffer
           (widget-put (alist-get acct -tree-widgets) :mailboxes mailboxes)
           (cl-remf accounts acct)
           (unless accounts (-set-mode-line-suffix nil))
           (let ((tree (alist-get acct -tree-widgets)))
             (when (widget-get tree :open)
               ;; Close and open to refresh children.
               ;; FIXME: Keep open/closed state of children as well, keep point.
               (widget-put tree :open nil)
               (widget-apply tree :action)))))))))

;;;###autoload
(defun minimail-show-mailboxes ()
  "Browse the mailbox tree of your email accounts."
  (interactive)
  (pop-to-buffer "*minimail-accounts*")
  (unless (derived-mode-p 'minimail-overview-mode)
    (minimail-overview-mode)
    (-overview-buffer-populate)))

;;; MUA definition

;;;###autoload
(define-mail-user-agent 'minimail
  #'-compose-mail
  #'message-send-and-exit
  #'message-kill-buffer
  'message-send-hook)

(defun -send-mail ()
  "Call `smtpmail-send-it' with parameters from the X-Minimail-Account header."
  (let* ((account (save-restriction
                    (message-narrow-to-headers-or-head)
                    (mail-fetch-field "X-Minimail-Account" nil nil nil t)))
         (props (or (cdr (assoc account minimail-accounts #'string=))
                    (user-error "Invalid Minimail account: %s" account)))
         (url (url-generic-parse-url (plist-get props :outgoing-url)))
         (smtpmail-store-queue-variables t)
         (smtpmail-smtp-server (url-host url))
         (smtpmail-smtp-user (cond ((url-user url)
                                    (url-unhex-string (url-user url)))
                                   ((plist-get props :mail-address))))
         (smtpmail-stream-type (pcase (url-type url)
                                 ("smtps" 'tls)
                                 ("smtp" 'starttls)
                                 (other (user-error "\
In `minimail-accounts', outgoing-url must have smtps or smtp scheme, \
got %s" other))))
         (smtpmail-smtp-service (or (url-portspec url)
                                    (pcase smtpmail-stream-type
                                      ('tls 465)
                                      ('starttls 587)))))
    (smtpmail-send-it)))

;;;###autoload
(defun -compose-mail (&optional to subject &rest rest)
  (pcase-let*
      ((mailbox (or (get-text-property (point) '-current-mailbox)
                    -current-mailbox))
       ;; Pick some account set up for sending, preferably the current
       ;; one.
       (`(,account . ,props)
        (or (seq-find (lambda (it) (plist-get (cdr it) :outgoing-url))
                      `(,(assq (car mailbox) minimail-accounts)
                        ,@minimail-accounts))
            (user-error "No mail account has been configured to send messages")))
       (drafts (or (plist-get props :drafts-mailbox)
                   (-find-mailbox-by-flag '\\Drafts
                                          (athunk-run-polling
                                           (-aget-mailbox-listing account)
                                           :message "Fetching mailbox information"
                                           :interval 0.1 :max-tries 100))))
       ;; Context for finding settings: the current mailbox if it
       ;; belongs to the account used for sending this email, else
       ;; just the sending account.
       (ctx (if (eq (car mailbox) account) mailbox account))
       (name (-settings-scalar-get :full-name ctx))
       (addr (-settings-scalar-get :mail-address ctx))
       (`(,sig . ,sigfile)
        (pcase (-settings-scalar-get :signature ctx)
          (`(file ,fname . nil) (cons t fname))
          (v (cons v message-signature-file))))
       (setup (make-symbol "minimail--setup")))
    (fset setup
          (lambda ()
            (setq-local -current-mailbox (cons account drafts)
                        user-full-name name
                        user-mail-address addr
                        message-send-mail-function #'-send-mail
                        message-signature sig
                        message-signature-file sigfile)))
    (let ((message-mail-user-agent nil))
      (add-hook 'message-mode-hook setup -90)
      (unwind-protect
          (apply #'message-mail to subject rest)
        (remove-hook 'message-mode-hook setup)))
    (message-replace-header "X-Minimail-Account" (symbol-name account))
    (message-sort-headers)
    (message-position-point)
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
