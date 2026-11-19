#!/usr/bin/env python3
"""
Convert a Zulip HTML page dump to plain text (the visible message thread).

Zero external dependencies — uses only the Python standard library.

Usage:
    python3 zulip_thread_extract.py input.html [output.txt]
"""

import sys
import re
from html.parser import HTMLParser
from html import unescape


# ---------------------------------------------------------------------------
# Minimal DOM built from stdlib HTMLParser
# ---------------------------------------------------------------------------

class Node:
    """A lightweight DOM node."""
    __slots__ = ('tag', 'attrs', 'children', 'parent', 'text')

    def __init__(self, tag='', attrs=None):
        self.tag = tag
        self.attrs = dict(attrs) if attrs else {}
        self.children = []
        self.parent = None
        self.text = ''  # for text nodes only (tag == '')

    @property
    def cls(self):
        return self.attrs.get('class', '')

    def has_class(self, c):
        return c in self.cls.split()

    def find_all(self, tag=None, class_=None):
        """Depth-first search for matching descendants."""
        for child in self.children:
            if child.tag == '':
                continue
            match = True
            if tag and child.tag != tag:
                match = False
            if class_ and not child.has_class(class_):
                match = False
            if match:
                yield child
            yield from child.find_all(tag, class_)

    def find(self, tag=None, class_=None):
        return next(self.find_all(tag, class_), None)

    def get_text(self):
        if self.tag == '':
            return self.text
        return ''.join(c.get_text() for c in self.children)


class DOMBuilder(HTMLParser):
    """Build a minimal DOM tree from HTML."""

    VOID_ELEMENTS = frozenset([
        'area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input',
        'link', 'meta', 'param', 'source', 'track', 'wbr',
    ])

    def __init__(self):
        super().__init__()
        self.root = Node('root')
        self._cur = self.root

    def handle_starttag(self, tag, attrs):
        node = Node(tag, attrs)
        node.parent = self._cur
        self._cur.children.append(node)
        if tag not in self.VOID_ELEMENTS:
            self._cur = node

    def handle_endtag(self, tag):
        # Walk up to find the matching open tag (tolerates misnesting)
        n = self._cur
        while n and n.tag != tag and n.parent:
            n = n.parent
        if n and n.parent:
            self._cur = n.parent

    def handle_data(self, data):
        t = Node()
        t.text = data
        t.parent = self._cur
        self._cur.children.append(t)

    def handle_entityref(self, name):
        self.handle_data(unescape(f'&{name};'))

    def handle_charref(self, name):
        self.handle_data(unescape(f'&#{name};'))


def parse_html(path):
    with open(path, 'r', encoding='utf-8') as f:
        html = f.read()
    builder = DOMBuilder()
    builder.feed(html)
    return builder.root


# ---------------------------------------------------------------------------
# Content extraction
# ---------------------------------------------------------------------------

SKIP_CLASSES = {
    'message_controls', 'message_length_controller',
    'code-buttons-container', 'copy_codeblock', 'code_external_link',
    'message_edit_notice', 'edit-notifications',
}

def should_skip(node):
    return bool(SKIP_CLASSES & set(node.cls.split()))


def extract_content(node):
    """Recursively convert a message_content node into readable text."""
    parts = []
    for child in node.children:
        # Text node
        if child.tag == '':
            parts.append(child.text)
            continue

        if should_skip(child):
            continue

        cls_set = set(child.cls.split())

        # Code block wrappers  (div.codehilite / div.zulip-code-block)
        if child.tag == 'div' and ({'codehilite', 'zulip-code-block'} & cls_set):
            code = child.find('code')
            lang = child.attrs.get('data-code-language', '')
            text = code.get_text() if code else child.get_text()
            parts.append(f'\n```{lang}\n{text}```\n')
            continue

        # <pre> (bare code blocks without wrapper div)
        if child.tag == 'pre':
            code = child.find('code')
            text = code.get_text() if code else child.get_text()
            parts.append(f'\n```\n{text}```\n')
            continue

        # Inline <code>
        if child.tag == 'code':
            parts.append(f'`{child.get_text()}`')
            continue

        # Paragraph
        if child.tag == 'p':
            inner = extract_content(child)
            parts.append(f'\n{inner}\n')
            continue

        # Line break
        if child.tag == 'br':
            parts.append('\n')
            continue

        # Links
        if child.tag == 'a':
            href = child.attrs.get('href', '')
            text = child.get_text().strip()
            if href and not href.startswith('#') and text:
                parts.append(f'[{text}]({href})')
            else:
                parts.append(text)
            continue

        # Block quotes
        if child.tag == 'blockquote':
            bq = extract_content(child).strip()
            parts.append('\n' + '\n'.join(f'> {l}' for l in bq.split('\n')) + '\n')
            continue

        # Lists
        if child.tag in ('ul', 'ol'):
            for i, li in enumerate(c for c in child.children if c.tag == 'li'):
                pfx = f'{i+1}.' if child.tag == 'ol' else '-'
                parts.append(f'\n{pfx} {extract_content(li).strip()}')
            parts.append('\n')
            continue

        # User mentions
        if 'user-mention' in cls_set:
            parts.append(f'@{child.get_text().strip().lstrip("@")}')
            continue

        # Emoji
        if 'emoji' in cls_set:
            alt = child.attrs.get('alt', '') or child.attrs.get('title', '')
            if alt:
                parts.append(alt)
            continue

        # Recurse into everything else
        parts.append(extract_content(child))

    return ''.join(parts)


# ---------------------------------------------------------------------------
# Thread extraction
# ---------------------------------------------------------------------------

def extract_thread(html_path, output_path=None):
    root = parse_html(html_path)

    # Find the message list
    msg_list = root.find('div', class_='message-list')
    if not msg_list:
        print("ERROR: Could not find message list.", file=sys.stderr)
        sys.exit(1)

    # Topic header
    header = msg_list.find('div', class_='message_header')
    stream_name = topic_name = date_str = ''
    if header:
        el = header.find('span', class_='message-header-stream-name')
        if el: stream_name = el.get_text().strip()
        el = header.find('span', class_='stream-topic-inner')
        if el: topic_name = el.get_text().strip()
        el = header.find('span', class_='recipient_row_date')
        if el:
            tr = el.find('span', class_='timerender-content')
            if tr:
                date_str = tr.attrs.get('data-tippy-content', '') or tr.get_text().strip()

    # Messages
    messages = []
    for row in msg_list.find_all('div', class_='message_row'):
        if not row.has_class('messagebox-includes-sender'):
            continue

        msg = {}

        sn = row.find('span', class_='sender_name_text')
        if sn:
            un = sn.find('span', class_='user-name')
            msg['sender'] = (un or sn).get_text().strip()

        tm = row.find('a', class_='message-time')
        if tm:
            msg['time'] = tm.get_text().strip()

        cd = row.find('div', class_='message_content')
        if cd:
            text = extract_content(cd)
            text = re.sub(r'\n{3,}', '\n\n', text).strip()
            msg['content'] = text

        # Reactions
        reactions = []
        for rx in row.find_all('div', class_='message_reaction'):
            em = rx.find('div', class_='emoji_alt_code')
            if em:
                reactions.append(em.get_text().strip())
            else:
                img = rx.find(tag='img')
                if img:
                    reactions.append(img.attrs.get('alt', ''))
            cnt = rx.find('span', class_='message_reaction_count')
            if cnt and reactions:
                c = cnt.get_text().strip()
                if c and c != '1':
                    reactions[-1] += f' x{c}'
        if reactions:
            msg['reactions'] = reactions

        if msg.get('content') or msg.get('sender'):
            messages.append(msg)

    # Format
    lines = [
        '=' * 70,
        f'# {stream_name} > {topic_name}',
    ]
    if date_str:
        lines.append(f'# Started: {date_str}')
    lines += [f'# Messages: {len(messages)}', '=' * 70, '']

    for msg in messages:
        lines.append(f'--- {msg.get("sender","?")}  [{msg.get("time","")}] ---')
        lines.append(msg.get('content', ''))
        if msg.get('reactions'):
            lines.append(f'  Reactions: {", ".join(msg["reactions"])}')
        lines.append('')

    result = '\n'.join(lines)
    if output_path:
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(result)
        print(f"Written {len(messages)} messages to {output_path}")
    else:
        print(result)


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} input.html [output.txt]")
        sys.exit(1)
    extract_thread(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else None)

