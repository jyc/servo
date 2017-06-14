#![allow(warnings, missing_docs)]
/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

//! Support for the [Properties & Values API][spec].
//!
//! [spec]: https://drafts.css-houdini.org/css-properties-values-api-1/

use cssparser::{Parser, Token};
use custom_properties::{Name};
use heapsize::HeapSizeOf;
use std::borrow::Cow;
use std::collections::{HashMap};
use std::default::Default;
use std::vec::Vec;

/// A registration for a custom property.
#[derive(HeapSizeOf)]
pub struct Registration {
    name: Name,
    syntax: (),
    inherits: bool,
    // Later maybe make this lazily parsed?
    initial_value: String,
}

/// A set of registered custom properties, stored on the document.
#[derive(Default, HeapSizeOf)]
pub struct RegisteredPropertySet {
    registrations: HashMap<Name, Registration>,
    generation: i32,
}

#[derive(Debug, Eq, HeapSizeOf, PartialEq)]
pub enum Type<'a> {
    Length,
    Number,
    Percentage,
    LengthPercentage,
    Color,
    Image,
    Url,
    Integer,
    Angle,
    Time,
    Resolution,
    TransformFunction,
    CustomIdent,
    SpecificIdentifier(Cow<'a, str>),
}

#[derive(Debug, Eq, HeapSizeOf, PartialEq)]
pub struct Term<'a> {
    typ: Type<'a>,
    list: bool,
}

#[derive(Debug, Eq, HeapSizeOf, PartialEq)]
pub enum Syntax<'a> {
    Anything,
    Disjunction(Vec<Term<'a>>),
}

impl<'a> Syntax<'a> {
    pub fn parse(input: &'a str) -> Result<Syntax<'a>, ()> {
        // Syntax strings are DOMStrings, but in Servo we assume they are valid UTF-8.
        // See https://doc.servo.org/script/dom/bindings/str/struct.DOMString.html .
        // This justifies iteration by |char|.

        // "Currently the answer is no - I've clarified the "literal ident" part to be specifically
        //  a name-start char followed by 0+ name chars. Would prefer to avoid having to do CSS
        //  parsing on the syntax string. ^_^"
        // https://github.com/w3c/css-houdini-drafts/issues/112

        // Any sequence consisting of a name-start code point, followed by zero or more name code
        // points, which matches the <custom-ident> production 
        // https://drafts.css-houdini.org/css-properties-values-api-1/#supported-syntax-strings
        // This generic data type is denoted by <custom-ident>, and represents any valid CSS
        // identifier that would not be misinterpreted as a pre-defined keyword in that property’s
        // value definition.
        // https://drafts.csswg.org/css-values-4/#identifier-value
        //
        // So! We just need to check for escapes, which are only introduced by backslashes, which
        // shouldn't show up anyhow.
        // https://drafts.csswg.org/css-syntax-3/#escaping
        let mut contains_backslash = false;
        for c in input.chars() {
            if c == '\\' {
                contains_backslash = true;
                break
            }
        }
        if contains_backslash {
            return Err(())
        }

        let mut syntax = None;

        let mut parser = Parser::new(input);

        #[derive(Debug)]
        enum State {
            AfterAsterisk,
            AfterOpenAngle,
            AfterPlus,
            AfterType { after_whitespace: bool },
            AfterTypeName,
            Start { after_bar: bool },
        }
        let mut state = State::Start { after_bar: false };

        fn push_type<'a>(syntax: &mut Option<Syntax<'a>>, t: Type<'a>) {
            if let Some(Syntax::Disjunction(ref mut ts)) = *syntax {
                ts.push(Term { typ: t, list: false })
            } else { panic!() }
        }

        fn expect_disjunction(syntax: &mut Option<Syntax>) {
            if let Some(Syntax::Disjunction(_)) = *syntax {
                // Good!
            } else {
                assert!(*syntax == None);
                *syntax = Some(Syntax::Disjunction(vec![]))
            }
        }

        fn handle_token<'a>(syntax: &mut Option<Syntax<'a>>, state: State, token: Token<'a>) -> Result<State, ()> {
            println!("{:?} - {:?}", state, token);
            match (state, token) {
                (_, Token::Comment(_)) => Err(()),

                (State::Start { .. }, Token::WhiteSpace(_)) => {
                    Ok(State::Start { after_bar: false })
                },
                (State::Start { after_bar: false }, Token::Delim('*')) => {
                    if syntax != &None {
                        Err(())
                    } else {
                        *syntax = Some(Syntax::Anything);
                        Ok(State::AfterAsterisk)
                    }
                },
                (State::Start { .. }, Token::Delim('<')) => {
                    expect_disjunction(syntax);
                    Ok(State::AfterOpenAngle)
                },
                (State::Start { .. }, Token::Ident(id)) => {
                    expect_disjunction(syntax);
                    match &*id {
                        "initial" | "inherit" | "unset" => Err(()),
                        _ => {
                            push_type(syntax, Type::SpecificIdentifier(id));
                            Ok(State::AfterType { after_whitespace: false })
                        }
                    }
                },
                (State::Start { .. }, _) => Err(()),

                (State::AfterOpenAngle, Token::Ident(id)) => {
                    push_type(syntax, match &*id {
                        "length" => Type::Length,
                        "number" => Type::Number,
                        "percentage" => Type::Percentage,
                        "length-percentage" => Type::LengthPercentage,
                        "color" => Type::Color,
                        "image" => Type::Image,
                        "url" => Type::Url,
                        "integer" => Type::Integer,
                        "angle" => Type::Angle,
                        "time" => Type::Time,
                        "resolution" => Type::Resolution,
                        "transform-function" => Type::TransformFunction,
                        "custom-ident" => Type::CustomIdent,
                        _ => return Err(())
                    });
                    Ok(State::AfterTypeName)
                },
                (State::AfterOpenAngle, _) => Err(()),

                (State::AfterTypeName, Token::Delim('>')) => {
                    Ok(State::AfterType { after_whitespace: false })
                },
                (State::AfterTypeName, _) => Err(()),

                (State::AfterType { .. }, Token::WhiteSpace(_)) => {
                    Ok(State::AfterType { after_whitespace: true })
                },
                (State::AfterType { after_whitespace: false }, Token::Delim('+')) => {
                    if let Some(Syntax::Disjunction(ref mut ts)) = *syntax {
                        ts.last_mut().unwrap().list = true
                    } else { panic!() }
                    Ok(State::AfterPlus)
                },
                (State::AfterType { .. }, Token::Delim('|')) => {
                    Ok(State::Start { after_bar: true })
                },
                (State::AfterType { .. }, _) => Err(()),

                (State::AfterAsterisk, Token::WhiteSpace(_)) => Ok(State::AfterAsterisk),
                (State::AfterAsterisk, _) => Err(()),

                (State::AfterPlus, Token::WhiteSpace(_)) => Ok(State::AfterPlus),
                (State::AfterPlus, Token::Delim('|')) => {
                    Ok(State::Start { after_bar: true })
                }
                (State::AfterPlus, _) => Err(()),
            }
        }

        loop {
            match parser.next_including_whitespace_and_comments() {
                Err(BasicParseError::EndOfInput) => {
                    match state {
                        State::Start { after_bar: false } |
                        State::AfterType { .. } |
                        State::AfterAsterisk |
                        State::AfterPlus => break,

                        State::Start { after_bar: true } |
                        State::AfterOpenAngle |
                        State::AfterTypeName => return Err(())
                    }
                },
                Err(_) => return Err(()),
                Ok(token) => {
                    match handle_token(&mut syntax, state, token) {
                        Ok(s) => state = s,
                        Err(()) => return Err(())
                    }
                }
            }
        }

        syntax.ok_or(())
    }
}
