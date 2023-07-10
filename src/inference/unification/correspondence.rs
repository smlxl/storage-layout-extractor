//! This module contains types and logic responsible for merging regions of an
//! EVM word. They exist due to the need to merge packed encodings during
//! unification, but may be otherwise useful.

use std::mem;

use itertools::Itertools;

use crate::inference::{
    expression::{Span, TE},
    unification::{Equality, Judgement, Merge},
};

/// This type implements an operation for creating a correspondence between two
/// sets of spans, and then merging said spans.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Correspondence {
    left_spans:  Vec<Span>,
    right_spans: Vec<Span>,
    events:      Vec<Event>,
    is_struct:   bool,
}

impl Correspondence {
    /// Creates a new correspondence between `left_spans` and `right_spans`.
    #[must_use]
    pub fn new(
        left_spans: impl Into<Vec<Span>>,
        right_spans: impl Into<Vec<Span>>,
        is_struct: bool,
    ) -> Self {
        let left_spans = left_spans.into();
        let right_spans = right_spans.into();
        let events = Event::of_spans(&left_spans, &right_spans);

        Self {
            left_spans,
            right_spans,
            events,
            is_struct,
        }
    }

    /// Merges the `left_spans` with the `right_spans`, returning [`None`] if
    /// they are not compatible.
    ///
    /// # Panics
    ///
    /// If a programmer bug has caused the processing of an end event while both
    /// left and right have smaller spans.
    #[must_use]
    pub fn merge(&self) -> Option<Merge> {
        // The output vector of spans
        let mut spans: Vec<Span> = Vec::new();
        let mut equalities: Vec<Equality> = Vec::new();
        let mut judgements: Vec<Judgement> = Vec::new();

        // Tracking for the current state of any ongoing spans
        let mut left: Option<Payload> = None;
        let mut right: Option<Payload> = None;

        // The function to process completed spans
        let mut submit = |payload: &mut Option<Payload>| {
            let payload = mem::take(payload);
            let payload = payload.expect("Attempted to submit nonexistent payload");

            match payload.smaller_spans.len() {
                0 => spans.push(payload.span),
                1 if payload
                    .smaller_spans
                    .first()
                    .expect("No element in vector of len 1")
                    .size
                    == payload.span.size =>
                {
                    // If there is only one other element of the same size, we can write out an
                    // equality between the two and push one of them into the spans
                    equalities.push(Equality::new(
                        payload.span.typ,
                        payload
                            .smaller_spans
                            .first()
                            .expect("No element in vector of len 1")
                            .typ,
                    ));
                    spans.push(payload.span);
                }
                _ => {
                    // If there are multiple smaller elements, we reduce the problem size by
                    // outputting a judgement that equates the larger span's type to the packed
                    // encoding of the smaller spans
                    judgements.push(Judgement::new(
                        payload.span.typ,
                        TE::packed_of(payload.smaller_spans.clone()),
                    ));
                    spans.push(payload.span);
                }
            }
        };

        // We merge things by going event-by-event over the events
        for event in &self.events {
            match event {
                Event::StartL { span } => match right {
                    Some(p)
                        if p.span.start_bit() != event.start()
                            && p.span.end_bit() < event.end() =>
                    {
                        return None;
                    }
                    _ => {
                        left = Some(Payload::new(*span));
                    }
                },
                Event::StartR { span } => match left {
                    Some(p)
                        if p.span.start_bit() != event.start()
                            && p.span.end_bit() < event.end() =>
                    {
                        return None;
                    }
                    _ => {
                        right = Some(Payload::new(*span));
                    }
                },
                Event::EndL { .. } => {
                    if let Some(right) = &mut right {
                        let old_left =
                            mem::take(&mut left).expect("Encountered end left without start left");
                        assert!(
                            old_left.smaller_spans().is_empty(),
                            "Encountered non-empty left spans"
                        );
                        let left = old_left.span;
                        right.add_smaller(left);
                    } else {
                        submit(&mut left);
                    }
                }
                Event::EndR { .. } => {
                    if let Some(left) = &mut left {
                        let old_right = mem::take(&mut right)
                            .expect("Encountered end right without start right");
                        assert!(
                            old_right.smaller_spans.is_empty(),
                            "Encountered non-empty right spans"
                        );
                        let right = old_right.span;
                        left.add_smaller(right);
                    } else {
                        submit(&mut right);
                    }
                }
            }
        }

        let expression = if self.is_struct {
            TE::struct_of
        } else {
            TE::packed_of
        }(spans);

        Some(Merge::new(expression, equalities, judgements))
    }
}

/// A payload that tracks the current state of each side in the form of a
/// correspondence between one larger span and potentially many smaller spans
/// that fall into it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Payload {
    /// The potentially larger span.
    pub span: Span,

    /// Any corresponding smaller spans that must be part of it if the merge is
    /// to be correct.
    pub smaller_spans: Vec<Span>,
}

impl Payload {
    /// Creates a new payload wrapping the provided `span`.
    #[must_use]
    pub fn new(span: Span) -> Self {
        let smaller_spans = Vec::new();
        Self {
            span,
            smaller_spans,
        }
    }

    /// Adds `span` as a smaller span to the current payload.
    pub fn add_smaller(&mut self, span: Span) {
        self.smaller_spans.push(span);
    }

    /// Gets the current smaller spans in the payload.
    #[must_use]
    pub fn smaller_spans(&self) -> &Vec<Span> {
        &self.smaller_spans
    }
}

/// The potential events in the event stream when merging two sets of spans.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Event {
    /// The start of `span` on the left side.
    StartL { span: Span },

    /// The end of `span` on the left side.
    EndL { start: usize, size: usize },

    /// The start of `span` on the right side.
    StartR { span: Span },

    /// The end of `span` on the right side.
    EndR { start: usize, size: usize },
}

impl Event {
    /// Creates a new start event for the left set of spans, wrapping the
    /// starting `span`
    #[must_use]
    pub fn start_l(span: Span) -> Self {
        Self::StartL { span }
    }

    /// Creates a new end event for the left set of spans, wrapping the provided
    /// `span`.
    #[must_use]
    pub fn end_l(span: &Span) -> Self {
        let start = span.end_bit();
        let size = span.size;
        Self::EndL { start, size }
    }

    /// Creates a new start event for the right set of spans, wrapping the
    /// starting `span`
    #[must_use]
    pub fn start_r(span: Span) -> Self {
        Self::StartR { span }
    }

    /// Creates a new end event for the right set of spans, wrapping the
    /// provided `span`.
    #[must_use]
    pub fn end_r(span: &Span) -> Self {
        let start = span.end_bit();
        let size = span.size;
        Self::EndR { start, size }
    }

    /// Creates a vector of events from the provided left and right spans,
    /// sorted according to the following criteria.
    ///
    /// # Sorting Criteria
    ///
    /// The events in the result of `of_spans` are sorted as follows:
    ///
    /// 1. Sort by the `offset` of the span first.
    /// 2. Breaking ties by ordering `end` events before `start` events.
    /// 3. Breaking ties by ordering by `size`.
    ///
    /// These sorting criteria are the ones required for the merging algorithm.
    #[must_use]
    pub fn of_spans(left_spans: &[Span], right_spans: &[Span]) -> Vec<Self> {
        left_spans
            .iter()
            .flat_map(|s| vec![Self::start_l(*s), Self::end_l(s)])
            .chain(
                right_spans
                    .iter()
                    .flat_map(|s| vec![Self::start_r(*s), Self::end_r(s)]),
            )
            .sorted_by_key(|e| {
                let event_key = match e {
                    Self::EndL { .. } | Self::EndR { .. } => 0,
                    Self::StartL { .. } | Self::StartR { .. } => 1,
                };
                (e.start(), event_key, e.size())
            })
            .collect()
    }

    /// Gets the start position for the event (where it is within the parent
    /// word).
    #[must_use]
    pub fn start(&self) -> usize {
        match self {
            Self::StartL { span } | Self::StartR { span } => span.offset,
            Self::EndL { start, .. } | Self::EndR { start, .. } => *start,
        }
    }

    /// Gets the end position of the event (where it ends in the parent word).
    #[must_use]
    pub fn end(&self) -> usize {
        match self {
            Self::StartL { span } | Self::StartR { span } => span.offset + span.size,
            Self::EndL { start, size } | Self::EndR { start, size } => start + size,
        }
    }

    /// Gets the size of the event (the space it takes up in the parent word).
    #[must_use]
    pub fn size(&self) -> usize {
        match self {
            Self::StartL { span } | Self::StartR { span } => span.size,
            Self::EndL { size, .. } | Self::EndR { size, .. } => *size,
        }
    }
}

#[cfg(test)]
mod test {
    use crate::inference::{
        expression::{Span, TE},
        state::TypeVariable,
        unification::{
            correspondence::{Correspondence, Event},
            Equality,
            Judgement,
        },
    };

    #[test]
    fn can_construct_events_from_spans_in_sorted_order() {
        // Create the left and right spans
        let span_1 = Span::new(unsafe { TypeVariable::new() }, 0, 64);
        let span_2 = Span::new(unsafe { TypeVariable::new() }, 192, 64);
        let span_3 = Span::new(unsafe { TypeVariable::new() }, 0, 128);
        let span_4 = Span::new(unsafe { TypeVariable::new() }, 128, 128);
        let left_spans = vec![span_1, span_2];
        let right_spans = vec![span_3, span_4];

        // Create events from the spans
        let events = Event::of_spans(&left_spans, &right_spans);
        assert_eq!(events.len(), 8);

        // Check that we get the correct events in the correct order
        assert_eq!(events[0], Event::start_l(span_1));
        assert_eq!(events[1], Event::start_r(span_3));
        assert_eq!(events[2], Event::end_l(&span_1));
        assert_eq!(events[3], Event::end_r(&span_3));
        assert_eq!(events[4], Event::start_r(span_4));
        assert_eq!(events[5], Event::start_l(span_2));
        assert_eq!(events[6], Event::end_l(&span_2));
        assert_eq!(events[7], Event::end_r(&span_4));
    }

    /// Tests the following scenario.
    ///
    /// ```text
    /// packed(span(0, 64), span(64, 64) + packed(span(0, 128), span(128, 128))
    ///          a            b                     c             d
    /// ```
    #[test]
    fn can_merge_simple_spans() {
        // Create the left and right spans
        let a_tv = unsafe { TypeVariable::new() };
        let a = Span::new(a_tv, 0, 64);
        let b_tv = unsafe { TypeVariable::new() };
        let b = Span::new(b_tv, 64, 64);
        let c_tv = unsafe { TypeVariable::new() };
        let c = Span::new(c_tv, 0, 128);
        let d_tv = unsafe { TypeVariable::new() };
        let d = Span::new(d_tv, 128, 128);
        let left_spans = vec![a, b];
        let right_spans = vec![c, d];

        // Create the correspondence
        let result = Correspondence::new(left_spans, right_spans, false).merge().unwrap();

        // Check the results
        assert!(result.equalities.is_empty());
        assert_eq!(result.judgements.len(), 1);

        assert_eq!(
            result.judgements[0],
            Judgement::new(c_tv, TE::packed_of(vec![a, b]))
        );

        assert_eq!(result.expression, TE::packed_of(vec![c, d]));
    }

    /// Tests the following scenario.
    ///
    /// ```text
    /// packed(span(128, 128)) + packed(span(0, 64), span(192, 64))
    ///          a                        b            c
    /// ```
    #[test]
    fn can_merge_strange_spans() {
        // Create the left and right spans
        let a_tv = unsafe { TypeVariable::new() };
        let a = Span::new(a_tv, 128, 128);
        let b_tv = unsafe { TypeVariable::new() };
        let b = Span::new(b_tv, 0, 64);
        let c_tv = unsafe { TypeVariable::new() };
        let c = Span::new(c_tv, 192, 64);
        let left_spans = vec![a];
        let right_spans = vec![b, c];

        // Create the correspondence
        let result = Correspondence::new(left_spans, right_spans, true).merge().unwrap();

        // Check the results
        assert!(result.equalities.is_empty());
        assert_eq!(result.judgements.len(), 1);

        assert_eq!(
            result.judgements[0],
            Judgement::new(a_tv, TE::packed_of(vec![c]))
        );

        assert_eq!(result.expression, TE::struct_of(vec![b, a]));
    }

    /// Tests the following scenario.
    ///
    /// ```text
    /// packed(span(0, 32), span(192, 32)) + packed(span(64, 64), span(224, 32))
    ///          a            b                       c             d
    /// ```
    #[test]
    fn can_merge_disjoint_spans() {
        // Create the left and right spans
        let a_tv = unsafe { TypeVariable::new() };
        let a = Span::new(a_tv, 0, 32);
        let b_tv = unsafe { TypeVariable::new() };
        let b = Span::new(b_tv, 192, 32);
        let c_tv = unsafe { TypeVariable::new() };
        let c = Span::new(c_tv, 64, 64);
        let d_tv = unsafe { TypeVariable::new() };
        let d = Span::new(d_tv, 224, 32);
        let left_spans = vec![a, b];
        let right_spans = vec![c, d];

        // Create the correspondence
        let result = Correspondence::new(left_spans, right_spans, false).merge().unwrap();

        // Check the results
        assert!(result.judgements.is_empty());
        assert!(result.equalities.is_empty());

        assert_eq!(result.expression, TE::packed_of(vec![a, c, b, d]));
    }

    /// Tests the following scenario.
    ///
    /// ```text
    /// packed(span(0, 64), span(192, 32)) + packed(span(128, 128))
    ///          a            b                       c
    /// ```
    #[test]
    fn can_merge_total_overlaps() {
        // Create the left and right spans
        let a_tv = unsafe { TypeVariable::new() };
        let a = Span::new(a_tv, 0, 64);
        let b_tv = unsafe { TypeVariable::new() };
        let b = Span::new(b_tv, 192, 32);
        let c_tv = unsafe { TypeVariable::new() };
        let c = Span::new(c_tv, 128, 128);
        let left_spans = vec![a, b];
        let right_spans = vec![c];

        // Create the correspondence
        let result = Correspondence::new(left_spans, right_spans, true).merge().unwrap();

        // Check the results
        assert!(result.equalities.is_empty());
        assert_eq!(result.judgements.len(), 1);

        assert_eq!(
            result.judgements[0],
            Judgement::new(c_tv, TE::packed_of(vec![b]))
        );

        assert_eq!(result.expression, TE::struct_of(vec![a, c]));
    }

    /// Tests the following scenario.
    ///
    /// ```text
    /// packed(span(0, 64), span(128, 64), span(192, 64)) + packed(span(0, 64), span(192, 64))
    ///          a            b              c                       d            e
    /// ```
    #[test]
    #[allow(clippy::many_single_char_names)] // Intentionally matches the spec above
    fn can_equate_spans_of_same_size() {
        // Create the left and right spans
        let a_tv = unsafe { TypeVariable::new() };
        let a = Span::new(a_tv, 0, 64);
        let b_tv = unsafe { TypeVariable::new() };
        let b = Span::new(b_tv, 128, 64);
        let c_tv = unsafe { TypeVariable::new() };
        let c = Span::new(c_tv, 192, 64);
        let d_tv = unsafe { TypeVariable::new() };
        let d = Span::new(d_tv, 0, 64);
        let e_tv = unsafe { TypeVariable::new() };
        let e = Span::new(e_tv, 192, 64);
        let left_spans = vec![a, b, c];
        let right_spans = vec![d, e];

        // Create the correspondence
        let result = Correspondence::new(left_spans, right_spans, true).merge().unwrap();

        // Check the results
        assert!(result.judgements.is_empty());
        assert_eq!(result.equalities.len(), 2);

        assert_eq!(result.equalities[0], Equality::new(d_tv, a_tv));
        assert_eq!(result.equalities[1], Equality::new(e_tv, c_tv));

        assert_eq!(result.expression, TE::struct_of(vec![d, b, e]));
    }
}
