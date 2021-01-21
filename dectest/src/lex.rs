// Copyright Materialize, Inc. All rights reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE file at the
// root of this repository, or online at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

pub struct LexBuf<'a> {
    pub s: &'a str,
}

impl<'a> LexBuf<'a> {
    pub fn new(s: &'a str) -> LexBuf {
        LexBuf { s }
    }

    pub fn peek(&self) -> Option<char> {
        self.s.chars().next()
    }

    pub fn consume(&mut self, s: &str) -> bool {
        let self_bytes = self.s.as_bytes();
        let b = s.as_bytes();
        if self_bytes.len() >= b.len() && self_bytes[..b.len()] == *b {
            self.s = &self.s[b.len()..];
            true
        } else {
            false
        }
    }
}

impl<'a> Iterator for LexBuf<'a> {
    type Item = char;

    fn next(&mut self) -> Option<char> {
        let ch = self.peek();
        if let Some(ch) = ch {
            self.s = &self.s[ch.len_utf8()..];
        }
        ch
    }
}
