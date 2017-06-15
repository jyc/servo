/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#![allow(missing_docs, warnings)] 

//! Support for the [Properties & Values API][spec].
//!
//! [spec]: https://drafts.css-houdini.org/css-properties-values-api-1/

use cssparser::{BasicParseError, Parser, ParserInput, Token};
use custom_properties::{self, Name};
use properties::longhands::transform;
use properties::{CSSWideKeyword};
use servo::url::SpecifiedUrl;
use servo_url::ServoUrl;
use std::collections::{HashMap};
use std::fmt;
use std::vec::Vec;
use style_traits::values::{OneOrMoreSeparated, SpaceSeparator, ToCss};
use values::computed;
use values::specified;

/// A registration for a custom property.
#[derive(HeapSizeOf)]
pub struct Registration {
    /// The custom property name, sans leading '--'.
    name: Name,
    /// The syntax of the custom property.
    syntax: Syntax,
    /// Whether the custom property is inherited down the DOM tree.
    inherits: bool,
    /// The initial value of the custom property.
    initial_value: String,
}

/// A versioned set of registered custom properties, stored on the document.
/// The [[registeredPropertySet]] of the spec. We keep track of the version to
/// know if we need to recompute which declarations are valid.
#[derive(Default, HeapSizeOf)]
pub struct RegisteredPropertySet {
    /// The set of registered custom properties. Names are sans leading '--'.
    registrations: HashMap<Name, Registration>,
    /// The current version. Must be incremented whenever `registrations` is
    /// modified.
    generation: i32,
}

/// A basic custom property syntax string for a custom property that, used to
/// build up disjunctions and list terms.
#[derive(Debug, Eq, HeapSizeOf, PartialEq)]
pub enum Type {
    /// Syntax to allow any valid <length> value.
    Length,
    /// Syntax to allow any valid <number> value.
    Number,
    /// Syntax to allow any valid <percentage> value.
    Percentage,
    /// Syntax to allow any valid <length> or <percentage> value, or any valid
    /// <calc()> expression combining <length> and <percentage> components.
    LengthPercentage,
    /// Syntax to allow any valid <color> value.
    Color,
    /// Syntax to allow any valid <image> value.
    Image,
    /// Syntax to allow any valid <url> value.
    Url,
    /// Syntax to allow any valid <integer> value.
    Integer,
    /// Syntax to allow any valid <angle> value.
    Angle,
    /// Syntax to allow any valid <time> value.
    Time,
    /// Syntax to allow any valid <resolution> value.
    Resolution,
    /// Syntax to allow any valid <transform-function> value.
    TransformFunction,
    /// Syntax to allow any valid <custom-ident> value.
    CustomIdent,
    /// Syntax to allow a specific identifier (matching the <custom-ident>
    /// production, compared codepoint-wise).
    SpecificIdentifier(String),
}

/// A custom property syntax string that is either some basic syntax string
/// (e.g. some <url> value) or some list term. A list term syntax string allows
/// a space-separated list of one or more repetitions of the type specified by
/// the string. Used to build up disjunctions.
#[derive(Debug, Eq, HeapSizeOf, PartialEq)]
pub struct Term {
    typ: Type,
    list: bool,
}

/// A custom property syntax string.
#[derive(Debug, Eq, HeapSizeOf, PartialEq)]
pub enum Syntax {
    /// Syntax to allow any token stream (written '*').
    Anything,
    /// Syntax to allow some disjunction of terms (possibly list terms), which
    /// allows any value matching one of the items in the combination, matched
    /// in specified order (written 'a | b | ...').
    Disjunction(Vec<Term>),
}

impl Syntax {
    /// Parse a syntax string given to `CSS.registerProperty`.
    pub fn from_string(input: &str) -> Result<Syntax, ()> {
        // Syntax strings are DOMStrings, but in Servo we assume they are valid
        // UTF-8. See
        // https://doc.servo.org/script/dom/bindings/str/struct.DOMString.html
        // . This justifies iteration by |char|.

        // Can identifiers in syntax strings contain escapes? No.
        //
        // "Currently the answer is no - I've clarified the "literal ident"
        //  part to be specifically a name-start char followed by 0+ name chars.
        //  Would prefer to avoid having to do CSS parsing on the syntax string.
        //  ^_^"
        // https://github.com/w3c/css-houdini-drafts/issues/112
        // 
        // A 'specific ident' is any sequence consisting of a name-start code
        // point, followed by zero
        // or more name code points, which matches the <custom-ident>
        // production
        // https://drafts.css-houdini.org/css-properties-values-api-1/#supported-syntax-strings
        //
        // ...
        // This generic data type is denoted by <custom-ident>, and represents
        // any valid CSS identifier that would not be misinterpreted as a
        // pre-defined keyword in that property’s value definition.
        // https://drafts.csswg.org/css-values-4/#identifier-value
        //
        // So! In order to make sure specific identifiers don't contain
        // escapes, we need to check for escapes, which are only introduced by
        // backslashes, which shouldn't show up anyhow.
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

        // The parsed syntax string, which we'll build up as we scan tokens.
        let mut syntax = None;

        // The syntax string isn't really CSS, but hopefully this maximizes
        // code reuse.
        let mut parser_input = ParserInput::new(input);
        let mut parser = Parser::new(&mut parser_input);

        #[derive(Debug)]
        enum State {
            // *.
            AfterAsterisk,
            // <.
            AfterOpenAngle,
            // +.
            AfterPlus,
            // <type>.
            // ident.
            AfterType { after_whitespace: bool },
            // <type.
            AfterTypeName,
            // .
            // |.
            Start { after_bar: bool },
        }

        let mut state = State::Start { after_bar: false };

        /// Add a `Type` to the disjunction. It might turn out this is a list
        /// term, in which case we'll modify the `Term` later.
        fn push_type(syntax: &mut Option<Syntax>, t: Type) {
            if let Some(Syntax::Disjunction(ref mut ts)) = *syntax {
                ts.push(Term { typ: t, list: false })
            } else { unreachable!() }
        }

        /// Signal that we expect to be parsing some term in a disjunction.
        fn expect_disjunction(syntax: &mut Option<Syntax>) {
            if let Some(Syntax::Disjunction(_)) = *syntax {
                // Good!
            } else {
                assert!(*syntax == None);
                *syntax = Some(Syntax::Disjunction(vec![]))
            }
        }

        /// Handle the next token in the syntax string (including whitespace).
        fn handle_token(syntax: &mut Option<Syntax>, state: State, token: Token) -> Result<State, ()> {
            debug!("{:?} - {:?}", state, token);
            match (state, token) {
                (_, Token::Comment(_)) => Err(()),

                (State::Start { .. }, Token::WhiteSpace(_)) => {
                    // Ignore whitespace.
                    Ok(State::Start { after_bar: false })
                },
                (State::Start { after_bar: false }, Token::Delim('*')) => {
                    // If we see a '*', that should be it (modulo whitespace).
                    if syntax != &None {
                        Err(())
                    } else {
                        *syntax = Some(Syntax::Anything);
                        Ok(State::AfterAsterisk)
                    }
                },
                (State::Start { .. }, Token::Delim('<')) => {
                    // A '<' should mean we're in the start of a '<type>'.
                    expect_disjunction(syntax);
                    Ok(State::AfterOpenAngle)
                },
                (State::Start { .. }, Token::Ident(id)) => {
                    // An identifier by itself should mean we're about to see a
                    // specific identifier. Note that for <custom-idents> we
                    // have that they "[must] not be misinterpreted as a
                    // pre-defined keyword in that property’s value
                    // definition". Here that means CSS-wide keywords!
                    expect_disjunction(syntax);
                    match CSSWideKeyword::from_ident(&id) {
                        Some(_) => Err(()),
                        None => {
                            push_type(syntax, Type::SpecificIdentifier(id.into_owned()));
                            Ok(State::AfterType { after_whitespace: false })
                        }
                    }
                },
                (State::Start { .. }, _) => Err(()),

                (State::AfterOpenAngle, Token::Ident(id)) => {
                    // We should be in something like '<length>' here.
                    // https://drafts.css-houdini.org/css-properties-values-api/#supported-syntax-strings
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
                    // This should be the end of something like '<length>'.
                    Ok(State::AfterType { after_whitespace: false })
                },
                (State::AfterTypeName, _) => Err(()),

                (State::AfterType { .. }, Token::WhiteSpace(_)) => {
                    // Ignore whitespace.
                    Ok(State::AfterType { after_whitespace: true })
                },
                (State::AfterType { after_whitespace: false }, Token::Delim('+')) => {
                    // We should be following some type.
                    // We should panic if we're not, because we should only get
                    // here from Start -> AfterOpenAngle -> AfterTypeName (in
                    // the case of something like '<length>') or
                    // Start (in the case of something like 'my-ident'), both
                    // of which should have pushed a type.
                    if let Some(Syntax::Disjunction(ref mut ts)) = *syntax {
                        ts.last_mut().unwrap().list = true
                    } else { unreachable!() }
                    Ok(State::AfterPlus)
                },
                (State::AfterType { .. }, Token::Delim('|')) => {
                    // Some other term in the disjunction should follow.
                    Ok(State::Start { after_bar: true })
                },
                (State::AfterType { .. }, _) => Err(()),

                (State::AfterAsterisk, Token::WhiteSpace(_)) => Ok(State::AfterAsterisk),
                (State::AfterAsterisk, _) => Err(()),
                (State::AfterPlus, Token::WhiteSpace(_)) => Ok(State::AfterPlus),
                (State::AfterPlus, Token::Delim('|')) => {
                    // Some other term in the disjunction should follow.
                    Ok(State::Start { after_bar: true })
                }
                (State::AfterPlus, _) => Err(()),
            }
        }

        // Loop over all of the tokens in the syntax string.
        loop {
            match parser.next_including_whitespace_and_comments() {
                Err(BasicParseError::EndOfInput) => {
                    match state {
                        State::Start { after_bar: false } |
                        State::AfterType { .. } |
                        State::AfterAsterisk |
                        State::AfterPlus => break,

                        // We shouldn't reach EOF in the middle of something.
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

    pub fn parse(&self, input: &str) -> Result<SpecifiedVariableValue, ()> {
        Err(())
    }
}

//#[derive(ToComputedValue)]
//looks like this is for computing sub-elements 
#[derive(ToCss)]
pub enum SpecifiedVariableValue {
    Length(specified::Length),
    Number(specified::Number),
    Percentage(specified::Percentage),
    LengthPercentage(specified::CalcLengthOrPercentage),
    Color(specified::Color),
    Image(specified::Image),
    // need tocss Url(SpecifiedUrl),
    Integer(specified::Integer),
    Angle(specified::Angle),
    Time(specified::Time),
    //Resolution(specified::Resolution),
    TransformFunction(transform::SpecifiedOperation),
    CustomIdent(String),
    SpecificIdent(String),
    TokenStream(custom_properties::SpecifiedValue),

    // `#[derive(ToCss)]` will otherwise generate `where
    // Vec<SpecifiedVariableValue>: ToCss`, which confuses the compiler.
    #[omit_to_css_bounds]
    List(Vec<SpecifiedVariableValue>),
}

impl OneOrMoreSeparated for SpecifiedVariableValue {
    type S = SpaceSeparator;
}

#[derive(ToCss)]
pub enum ComputedVariableValue {
    Length(computed::Length),
    Number(computed::Number),
    Percentage(computed::Percentage),
    LengthPercentage(computed::CalcLengthOrPercentage),
    Color(computed::Color),
    Image(computed::Image),
    // need tocss Url(ServoUrl),
    Integer(computed::Integer),
    Angle(computed::Angle),
    Time(computed::Time),
    //Resolution(specified::Resolution),
    // This should only contain computed values, though (e.g. no calc).
    TransformFunction(transform::SpecifiedOperation),
    CustomIdent(String),
    SpecificIdent(String),
    TokenStream(custom_properties::SpecifiedValue),

    // `#[derive(ToCss)]` will otherwise generate `where
    // Vec<SpecifiedVariableValue>: ToCss`, which confuses the compiler.
    #[omit_to_css_bounds]
    List(Vec<ComputedVariableValue>),
}

impl OneOrMoreSeparated for ComputedVariableValue {
    type S = SpaceSeparator;
}
