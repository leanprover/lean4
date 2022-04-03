var Alectryon;
(function(Alectryon) {
    (function (slideshow) {
        function anchor(sentence) { return "#" + sentence.id; }

        function current_sentence() { return slideshow.sentences[slideshow.pos]; }

        function unhighlight() {
            var sentence = current_sentence();
            if (sentence) sentence.classList.remove("alectryon-target");
            slideshow.pos = -1;
        }

        function highlight(sentence) {
            sentence.classList.add("alectryon-target");
        }

        function scroll(sentence) {
            // Put the top of the current fragment close to the top of the
            // screen, but scroll it out of view if showing it requires pushing
            // the sentence past half of the screen.  If sentence is already in
            // a reasonable position, don't move.
            var parent = sentence.parentElement;
            /* We want to scroll the whole document, so start at root… */
            while (parent && !parent.classList.contains("alectryon-root"))
                parent = parent.parentElement;
            /* … and work up from there to find a scrollable element.
               parent.scrollHeight can be greater than parent.clientHeight
               without showing scrollbars, so we add a 10px buffer. */
            while (parent && parent.scrollHeight <= parent.clientHeight + 10)
                parent = parent.parentElement;
            /* <body> and <html> elements can have their client rect overflow
             * the window if their height is unset, so scroll the window
             * instead */
            if (parent && (parent.nodeName == "BODY" || parent.nodeName == "HTML"))
                parent = null;

            var rect = function(e) { return e.getBoundingClientRect(); };
            var parent_box = parent ? rect(parent) : { y: 0, height: window.innerHeight },
                sentence_y = rect(sentence).y - parent_box.y,
                fragment_y = rect(sentence.parentElement).y - parent_box.y;

            // The assertion below sometimes fails for the first element in a block.
            // console.assert(sentence_y >= fragment_y);

            if (sentence_y < 0.1 * parent_box.height ||
                sentence_y > 0.7 * parent_box.height) {
                (parent || window).scrollBy(
                    0, Math.max(sentence_y - 0.5 * parent_box.height,
                                fragment_y - 0.1 * parent_box.height));
            }
        }

        function highlighted(pos) {
            return slideshow.pos == pos;
        }

        function navigate(pos, inhibitScroll) {
            unhighlight();
            slideshow.pos = Math.min(Math.max(pos, 0), slideshow.sentences.length - 1);
            var sentence = current_sentence();
            highlight(sentence);
            if (!inhibitScroll)
                scroll(sentence);
        }

        var keys = {
            PAGE_UP: 33,
            PAGE_DOWN: 34,
            ARROW_UP: 38,
            ARROW_DOWN: 40,
            h: 72, l: 76, p: 80, n: 78
        };

        function onkeydown(e) {
            e = e || window.event;
            if (e.ctrlKey || e.metaKey) {
                if (e.keyCode == keys.ARROW_UP)
                    slideshow.previous();
                else if (e.keyCode == keys.ARROW_DOWN)
                    slideshow.next();
                else
                    return;
            } else {
                // if (e.keyCode == keys.PAGE_UP || e.keyCode == keys.p || e.keyCode == keys.h)
                //     slideshow.previous();
                // else if (e.keyCode == keys.PAGE_DOWN || e.keyCode == keys.n || e.keyCode == keys.l)
                //     slideshow.next();
                // else
                return;
            }
            e.preventDefault();
        }

        function start() {
            slideshow.navigate(0);
        }

        function toggleHighlight(idx) {
            if (highlighted(idx))
                unhighlight();
            else
                navigate(idx, true);
        }

        function handleClick(evt) {
            if (evt.ctrlKey || evt.metaKey) {
                var sentence = evt.currentTarget;

                // Ensure that the goal is shown on the side, not inline
                var checkbox = sentence.getElementsByClassName("alectryon-toggle")[0];
                if (checkbox)
                    checkbox.checked = false;

                toggleHighlight(sentence.alectryon_index);
                evt.preventDefault();
            }
        }

        function init() {
            document.onkeydown = onkeydown;
            slideshow.pos = -1;
            slideshow.sentences = Array.from(document.getElementsByClassName("alectryon-sentence"));
            slideshow.sentences.forEach(function (s, idx) {
                s.addEventListener('click', handleClick, false);
                s.alectryon_index = idx;
            });
        }

        slideshow.start = start;
        slideshow.end = unhighlight;
        slideshow.navigate = navigate;
        slideshow.next = function() { navigate(slideshow.pos + 1); };
        slideshow.previous = function() { navigate(slideshow.pos + -1); };
        window.addEventListener('DOMContentLoaded', init);
    })(Alectryon.slideshow || (Alectryon.slideshow = {}));

    (function (styles) {
        var styleNames = ["centered", "floating", "windowed"];

        function className(style) {
            return "alectryon-" + style;
        }

        function setStyle(style) {
            var root = document.getElementsByClassName("alectryon-root")[0];
            styleNames.forEach(function (s) {
                root.classList.remove(className(s)); });
            root.classList.add(className(style));
        }

        function init() {
            var banner = document.getElementsByClassName("alectryon-banner")[0];
            if (banner) {
                banner.append(" Style: ");
                styleNames.forEach(function (styleName, idx) {
                    var s = styleName;
                    var a = document.createElement("a");
                    a.onclick = function() { setStyle(s); };
                    a.append(styleName);
                    if (idx > 0) banner.append("; ");
                    banner.appendChild(a);
                });
                banner.append(".");
            }
        }

        window.addEventListener('DOMContentLoaded', init);

        styles.setStyle = setStyle;
    })(Alectryon.styles || (Alectryon.styles = {}));
})(Alectryon || (Alectryon = {}));

function setHidden(elements, isVisible, token) {
    for (let i = 0; i < elements.length; i++) {
        if (isVisible) {
            elements[i].classList.remove(token)
        } else {
            elements[i].classList.add(token)
        }
    }
}

function toggleShowTypes(checkbox) {
    setHidden(document.getElementsByClassName("alectryon-io"), checkbox.checked, "type-info-hidden")
}

function toggleShowGoals(checkbox) {
    setHidden(document.getElementsByClassName("alectryon-io"), checkbox.checked, "output-hidden")
}