export interface UiBatchHeader { magic: number; version: number; headerSize: number; recordSize: number; count: number; recordsPtr: number; overflowed: number }
export declare const UI_ABI: Readonly<{ magic: number; version: number; headerSize: number; recordSize: number; effect: Readonly<Record<string, number>>; handler: Readonly<Record<string, number>> }>;
export declare function readUiBatch(memory: WebAssembly.Memory, ptr: number): UiBatchHeader;
