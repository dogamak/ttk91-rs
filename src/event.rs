//! Event handling.
//!
//! This library exposes an event-based interface for reacting
//! to the state changes of the emulator in real-time. [EventListeners](EventListener)
//! can be registered on the [Emulator](crate::emulator::Emulator) with the
//! [add_listener](crate::emulator::Emulator::add_listener) method.
//!
//! A blanket implementation of [EventListener] for all `Fn(&Event)` is provided.

use crate::instruction::Register;

/// Represents an event that occurred while executing a program.
pub enum Event {
    /// The program triggered a supervisor call.
    SupervisorCall {
        /// The code of the supervisor call.
        code: u16,
    },

    /// The program modified a memory location.
    MemoryChange {
        /// The address of the changed memory location.
        address: u16,

        /// New value of the changed memory location.
        data: i32,
    },

    /// The program modified a register.
    RegisterChange {
        /// The register which was modified.
        register: Register,

        /// The new value of the register.
        data: i32,
    },
}

/// Trait for consuming events.
pub trait EventListener {
    /// Called whenever a new event has been created.
    fn event(&mut self, event: &Event);
}

impl<F> EventListener for F where F: Fn(&Event) {
    fn event(&mut self, event: &Event) {
        self(event)
    }
}

pub(crate) struct EventDispatcher {
    listeners: Vec<Box<dyn EventListener>>,
}

impl EventDispatcher {
    pub fn new() -> EventDispatcher {
        EventDispatcher {
            listeners: Vec::new(),
        }
    }

    pub fn add_listener<L: EventListener + 'static>(&mut self, listener: L) {
        self.listeners.push(Box::new(listener) as Box<dyn EventListener>)
    }

    pub fn dispatch(&mut self, event: Event) {
        for listener in &mut self.listeners {
            listener.event(&event);
        }
    }
}

