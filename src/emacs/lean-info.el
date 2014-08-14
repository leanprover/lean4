;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'cl-lib)
(require 'lean-util)
(require 'lean-debug)

;; Type Information
;; ----------------
(defun lean-typeinfo-type (typeinfo)
  (cl-first typeinfo))
(defun lean-typeinfo-p (typeinfo)
  (equal (lean-typeinfo-type typeinfo) 'TYPE))
(defun lean-typeinfo-pos (typeinfo)
  (cl-second typeinfo))
(defun lean-typeinfo-str-p (str)
  (string-prefix-p "-- TYPE|" str))
(defun lean-typeinfo-str-seq-p (seq)
  (lean-typeinfo-str-p (cl-first seq)))
(defun lean-typeinfo-parse-header (str)
  (let ((items (split-string str "|")))
    (list (string-to-number (cl-second items))
          (string-to-number (cl-third items)))))
(defun lean-typeinfo-parse (seq)
  (let ((header (lean-typeinfo-parse-header (car seq)))
        (body (cdr seq)))
    `(TYPE ,header ,body)))
(defun lean-typeinfo-body (typeinfo)
  (cl-third typeinfo))
(defun lean-typeinfo-body-str (typeinfo)
  (string-join (lean-typeinfo-body typeinfo) "\n"))

;; -- Test
(cl-assert (lean-typeinfo-str-p "-- TYPE|121|2"))
(cl-assert (equal (lean-typeinfo-parse-header "-- TYPE|121|2")
                  '(121 2)))
(cl-assert (lean-typeinfo-str-seq-p '("-- TYPE|121|2" "not (eq zero (succ m'))" "→ decidable (eq zero (succ m'))")))
(cl-assert (equal (lean-typeinfo-parse '("-- TYPE|121|2" "not (eq zero (succ m'))" "→ decidable (eq zero (succ m'))"))
                  '(TYPE
                    (121 2)
                    ("not (eq zero (succ m'))"
                     "→ decidable (eq zero (succ m'))"))))
(cl-assert (equal
            (lean-typeinfo-pos
             (lean-typeinfo-parse '("-- TYPE|121|2" "not (eq zero (succ m'))" "→ decidable (eq zero (succ m'))")))
            '(121 2)))

;; Overload Information
;; --------------------

(defun lean-overload-type (overload)
  (cl-first overload))
(defun lean-overload-p (overload)
  (equal (lean-overload-type overload) 'OVERLOAD))
(defun lean-overload-pos (overload)
  (cl-second overload))
(defun lean-overload-names (overload)
  (cl-loop for seq in (cl-third overload)
           collect (string-join seq "\n")))
(defun lean-overload-str-p (str)
  (string-prefix-p "-- OVERLOAD|" str))
(defun lean-overload-str-seq-p (seq)
  (lean-overload-str-p (cl-first seq)))
(defun lean-overload-parse-header (str)
  (let ((items (split-string str "|")))
    (list (string-to-number (cl-second items))
          (string-to-number (cl-third items)))))
(defun lean-overload-parse (seq)
  (let ((header (lean-overload-parse-header (car seq)))
        (body (lean-split-seq (cdr seq) "--")))
    `(OVERLOAD ,header ,body)))

;; -- Test
(cl-assert (lean-overload-str-p "-- OVERLOAD|121|2"))
(cl-assert (equal (lean-overload-parse-header "-- OVERLOAD|121|2")
                  '(121 2)))
(cl-assert (lean-overload-str-seq-p '("-- OVERLOAD|121|2" "not (eq zero (succ m'))" "→ decidable (eq zero (succ m'))")))
(cl-assert
 (equal
  (lean-overload-parse
   '("-- OVERLOAD|121|2"
     "not (eq zero (succ m'))"
     "→ decidable (eq zero (succ m'))"
     "--"
     "not (eq one (succ m'))"
     "→ decidable (eq zero (succ m'))"
     "--"
     "not (eq two (succ m'))"
     "→ decidable (eq zero (succ m'))"))
  '(OVERLOAD (121 2)
             (("not (eq zero (succ m'))" "→ decidable (eq zero (succ m'))")
              ("not (eq one (succ m'))" "→ decidable (eq zero (succ m'))")
              ("not (eq two (succ m'))" "→ decidable (eq zero (succ m'))")))))
(cl-assert (equal
            (lean-overload-pos
             (lean-overload-parse
              '("-- OVERLOAD|121|2"
                "not (eq zero (succ m'))"
                "→ decidable (eq zero (succ m'))"
                "--"
                "not (eq one (succ m'))"
                "→ decidable (eq zero (succ m'))"
                "--"
                "not (eq two (succ m'))"
                "→ decidable (eq zero (succ m'))")))
            '(121 2)))

(cl-assert (equal (lean-overload-names (lean-overload-parse
                                        '("-- OVERLOAD|121|2"
                                          "not (eq zero (succ m'))"
                                          "→ decidable (eq zero (succ m'))"
                                          "--"
                                          "not (eq one (succ m'))"
                                          "→ decidable (eq zero (succ m'))"
                                          "--"
                                          "not (eq two (succ m'))"
                                          "→ decidable (eq zero (succ m'))")))
                  '("not (eq zero (succ m'))\n→ decidable (eq zero (succ m'))"
                    "not (eq one (succ m'))\n→ decidable (eq zero (succ m'))"
                    "not (eq two (succ m'))\n→ decidable (eq zero (succ m'))")))

;; Basic
;; -----
(defun lean-info-type (info)
  (cl-first info))
(defun lean-info-ack-str-p (str)
  (string= "-- ACK" str))
(defun lean-info-endinfo-str-p (str)
  (string= "-- ENDINFO" str))
(defun lean-info-pos (info)
  (cl-case (lean-info-type info)
    (TYPE     (lean-typeinfo-pos info))
    (OVERLOAD (lean-overload-pos info))))
(defun lean-info-line-number (info)
  (cl-first (lean-info-pos info)))
(defun lean-info-column (info)
  (cl-second (lean-info-pos info)))

;; -- test
(cl-assert (equal
            (lean-info-pos
             (lean-typeinfo-parse '("-- TYPE|121|2" "not (eq zero (succ m'))" "→ decidable (eq zero (succ m'))")))
            '(121 2)))
(cl-assert (equal
            (lean-info-pos
             (lean-overload-parse
              '("-- OVERLOAD|121|2"
                "not (eq zero (succ m'))"
                "→ decidable (eq zero (succ m'))"
                "--"
                "not (eq one (succ m'))"
                "→ decidable (eq zero (succ m'))"
                "--"
                "not (eq two (succ m'))"
                "→ decidable (eq zero (succ m'))")))
            '(121 2)))

;; Infolist Parsing
;; ================
(defun lean-infolist-split-lines (lines)
  "Split lines into list of list of strings

Use \"-- ACK\" as a delim and stop processing when it encounters \"-- ENDINFO\""
  (lean-split-seq-if
   (split-string lines "\n")
   'lean-info-ack-str-p
   '(lambda (x) (not (lean-info-endinfo-str-p x)))))
(defun lean-infolist-filter-seq (seq)
  "Filter warning and error messages"
  (cl-loop for line in seq
           when (and (not (search "warning:" line))
                     (not (search "error:" line)))
           collect line))

(defun lean-infolist-parse (lines)
  "TODO(soonhok): fill this"
  (let ((string-seq-seq (lean-infolist-filter-seq (lean-infolist-split-lines lines))))
    (cl-loop for string-seq in string-seq-seq
             when string-seq
             collect (cond
                      ((lean-typeinfo-str-seq-p string-seq) (lean-typeinfo-parse string-seq))
                      ((lean-overload-str-seq-p string-seq) (lean-overload-parse string-seq))))))

;; -- test
(cl-assert
 (equal (lean-infolist-parse
         (concat "-- TYPE|15|38" "\n"
                 "num" "\n"
                 "-- ACK" "\n"
                 "-- TYPE|15|40" "\n"
                 "num → num → Prop" "\n"
                 "-- ACK" "\n"
                 "-- OVERLOAD|15|42" "\n"
                 "f" "\n"
                 "--" "\n"
                 "foo.f" "\n"
                 "-- ACK" "\n"
                 "-- TYPE|15|42" "\n"
                 "num → num" "\n"
                 "-- ACK" "\n"
                 "-- TYPE|15|44" "\n"
                 "num" "\n"
                 "-- ACK" "\n"
                 "-- ENDINFO" "\n"))
        '((TYPE (15 38) ("num"))
          (TYPE (15 40) ("num → num → Prop"))
          (OVERLOAD (15 42) (("f")
                             ("foo.f")))
          (TYPE (15 42) ("num → num"))
          (TYPE (15 44) ("num")))))
(cl-assert
 (equal
  (lean-infolist-parse
   (concat
    "-- TYPE|121|2\nnot (eq zero (succ m')) → decidable (eq zero (succ m'))" "\n"
    "-- ACK" "\n"
    "-- TYPE|121|7\nne (succ m') zero → ne zero (succ m')" "\n"
    "-- ACK" "\n"
    "-- TYPE|121|16" "\n"
    "∀ (n : nat), ne (succ n) zero" "\n"
    "-- ACK" "\n"
    "-- TYPE|121|29" "\n"
    "nat" "\n"
    "-- ACK" "\n"
    "-- OVERLOAD|121|2" "\n"
    "not (eq zero (succ m'))" "\n"
    "→ decidable (eq zero (succ m'))" "\n"
    "--" "\n"
    "not (eq one (succ m'))" "\n"
    "→ decidable (eq one (succ m'))" "\n"
    "--" "\n"
    "not (eq two (succ m'))" "\n"
    "→ decidable (eq two (succ m'))" "\n"
    "-- ENDINFO" "\n"))
  '((TYPE (121 2) ("not (eq zero (succ m')) → decidable (eq zero (succ m'))"))
    (TYPE (121 7) ("ne (succ m') zero → ne zero (succ m')"))
    (TYPE (121 16) ("∀ (n : nat), ne (succ n) zero"))
    (TYPE (121 29) ("nat"))
    (OVERLOAD (121 2) (("not (eq zero (succ m'))" "→ decidable (eq zero (succ m'))")
                       ("not (eq one (succ m'))" "→ decidable (eq one (succ m'))")
                       ("not (eq two (succ m'))" "→ decidable (eq two (succ m'))"))))))
(provide 'lean-info)
