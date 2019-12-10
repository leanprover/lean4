// Lean compiler output
// Module: Init.Lean.Elab.Frontend
// Imports: Init.Lean.Elab.Import Init.Lean.Elab.Command
#include "runtime/lean.h"
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_Parser_mkParserContextCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Frontend_1__getCmdContext(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_ModuleParserState_inhabited___closed__1;
lean_object* l_Lean_Elab_Frontend_runCommandElabM(lean_object*);
lean_object* l_Lean_Elab_logElabException___at_Lean_Elab_Command_elabInitQuot___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Frontend_processCommandsAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_processHeader(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*);
extern lean_object* l_Lean_Elab_parseImports___closed__1;
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseCommand___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Frontend_processCommandsAux___boxed(lean_object*);
lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_testFrontend(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Frontend_updateCmdPos(lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Frontend_runCommandElabM___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Frontend_processCommand(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Frontend_processCommandsAux___main(lean_object*);
lean_object* l___private_Init_Lean_Elab_Frontend_1__getCmdContext___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
lean_object* l_Lean_Elab_Frontend_processCommandsAux___main___boxed(lean_object*);
lean_object* l_Lean_Elab_Frontend_processCommandsAux(lean_object*);
lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isExitCommand(lean_object*);
lean_object* l_Lean_Elab_Frontend_processCommandsAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Frontend_runCommandElabM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Frontend_updateCmdPos___boxed(lean_object*);
uint8_t l_Lean_Parser_isEOI(lean_object*);
lean_object* l_Lean_Elab_process(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Frontend_updateCmdPos___rarg(lean_object*);
lean_object* l_Lean_Elab_Frontend_processCommands(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Frontend_1__getCmdContext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_Frontend_1__getCmdContext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Elab_Frontend_1__getCmdContext(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Frontend_runCommandElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = l___private_Init_Lean_Elab_Frontend_1__getCmdContext(x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_apply_2(x_1, x_6, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 1);
lean_ctor_set(x_5, 0, x_11);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_9);
lean_ctor_set(x_5, 0, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_9, 1);
lean_ctor_set(x_5, 0, x_16);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
lean_ctor_set(x_5, 0, x_18);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_5);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_22 = lean_apply_2(x_1, x_6, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_21);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_30 = x_22;
} else {
 lean_dec_ref(x_22);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_21);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_Elab_Frontend_runCommandElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Frontend_runCommandElabM___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Frontend_runCommandElabM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Frontend_runCommandElabM___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = l___private_Init_Lean_Elab_Frontend_1__getCmdContext(x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = l_Lean_Elab_Command_elabCommand(x_1, x_6, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 1);
lean_ctor_set(x_5, 0, x_11);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_9);
lean_ctor_set(x_5, 0, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_9, 1);
lean_ctor_set(x_5, 0, x_16);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
lean_ctor_set(x_5, 0, x_18);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_5);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_22 = l_Lean_Elab_Command_elabCommand(x_1, x_6, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_21);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_30 = x_22;
} else {
 lean_dec_ref(x_22);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_21);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Frontend_elabCommandAtFrontend(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Frontend_updateCmdPos___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_3, 2);
lean_dec(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_ctor_set(x_3, 2, x_7);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_13);
lean_ctor_set(x_1, 0, x_15);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_1);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 3);
lean_inc(x_22);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 x_23 = x_18;
} else {
 lean_dec_ref(x_18);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 4, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_19);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
lean_object* l_Lean_Elab_Frontend_updateCmdPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Frontend_updateCmdPos___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Frontend_updateCmdPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Frontend_updateCmdPos(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Frontend_processCommand(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Elab_Frontend_updateCmdPos___rarg(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_1);
lean_inc(x_10);
x_12 = l_Lean_Parser_parseCommand___main(x_10, x_1, x_8, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_7, 1, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Parser_isEOI(x_14);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Parser_isExitCommand(x_14);
if (x_19 == 0)
{
lean_object* x_20; 
lean_free_object(x_3);
x_20 = l_Lean_Elab_Frontend_elabCommandAtFrontend(x_14, x_1, x_17);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = 0;
x_24 = lean_box(x_23);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_31 = l___private_Init_Lean_Elab_Frontend_1__getCmdContext(x_1, x_30);
lean_dec(x_1);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = l_Lean_Elab_logElabException___at_Lean_Elab_Command_elabInitQuot___spec__1(x_29, x_33, x_35);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_36, 1);
x_39 = lean_ctor_get(x_36, 0);
lean_dec(x_39);
lean_ctor_set(x_32, 0, x_38);
x_40 = 0;
x_41 = lean_box(x_40);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 0, x_41);
return x_36;
}
else
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_dec(x_36);
lean_ctor_set(x_32, 0, x_42);
x_43 = 0;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_32);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_32, 0);
x_47 = lean_ctor_get(x_32, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_32);
x_48 = l_Lean_Elab_logElabException___at_Lean_Elab_Command_elabInitQuot___spec__1(x_29, x_33, x_46);
lean_dec(x_33);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_47);
x_52 = 0;
x_53 = lean_box(x_52);
if (lean_is_scalar(x_50)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_50;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
}
else
{
uint8_t x_55; lean_object* x_56; 
lean_dec(x_14);
lean_dec(x_1);
x_55 = 1;
x_56 = lean_box(x_55);
lean_ctor_set(x_3, 1, x_17);
lean_ctor_set(x_3, 0, x_56);
return x_3;
}
}
else
{
uint8_t x_57; lean_object* x_58; 
lean_dec(x_14);
lean_dec(x_1);
x_57 = 1;
x_58 = lean_box(x_57);
lean_ctor_set(x_3, 1, x_17);
lean_ctor_set(x_3, 0, x_58);
return x_3;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_59 = lean_ctor_get(x_7, 0);
x_60 = lean_ctor_get(x_7, 1);
x_61 = lean_ctor_get(x_7, 2);
x_62 = lean_ctor_get(x_7, 3);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_7);
lean_inc(x_1);
lean_inc(x_59);
x_63 = l_Lean_Parser_parseCommand___main(x_59, x_1, x_8, x_60);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_59);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_61);
lean_ctor_set(x_68, 3, x_62);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
x_70 = l_Lean_Parser_isEOI(x_65);
if (x_70 == 0)
{
uint8_t x_71; 
x_71 = l_Lean_Parser_isExitCommand(x_65);
if (x_71 == 0)
{
lean_object* x_72; 
lean_free_object(x_3);
x_72 = l_Lean_Elab_Frontend_elabCommandAtFrontend(x_65, x_1, x_69);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_1);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
x_75 = 0;
x_76 = lean_box(x_75);
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_74;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_73);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; 
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_dec(x_72);
x_80 = l___private_Init_Lean_Elab_Frontend_1__getCmdContext(x_1, x_79);
lean_dec(x_1);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_85 = x_81;
} else {
 lean_dec_ref(x_81);
 x_85 = lean_box(0);
}
x_86 = l_Lean_Elab_logElabException___at_Lean_Elab_Command_elabInitQuot___spec__1(x_78, x_82, x_83);
lean_dec(x_82);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_85;
}
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_84);
x_90 = 0;
x_91 = lean_box(x_90);
if (lean_is_scalar(x_88)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_88;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
return x_92;
}
}
else
{
uint8_t x_93; lean_object* x_94; 
lean_dec(x_65);
lean_dec(x_1);
x_93 = 1;
x_94 = lean_box(x_93);
lean_ctor_set(x_3, 1, x_69);
lean_ctor_set(x_3, 0, x_94);
return x_3;
}
}
else
{
uint8_t x_95; lean_object* x_96; 
lean_dec(x_65);
lean_dec(x_1);
x_95 = 1;
x_96 = lean_box(x_95);
lean_ctor_set(x_3, 1, x_69);
lean_ctor_set(x_3, 0, x_96);
return x_3;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_97 = lean_ctor_get(x_3, 1);
lean_inc(x_97);
lean_dec(x_3);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_98, 2);
lean_inc(x_102);
x_103 = lean_ctor_get(x_98, 3);
lean_inc(x_103);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 lean_ctor_release(x_98, 2);
 lean_ctor_release(x_98, 3);
 x_104 = x_98;
} else {
 lean_dec_ref(x_98);
 x_104 = lean_box(0);
}
lean_inc(x_1);
lean_inc(x_100);
x_105 = l_Lean_Parser_parseCommand___main(x_100, x_1, x_99, x_101);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
if (lean_is_scalar(x_104)) {
 x_110 = lean_alloc_ctor(0, 4, 0);
} else {
 x_110 = x_104;
}
lean_ctor_set(x_110, 0, x_100);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_110, 2, x_102);
lean_ctor_set(x_110, 3, x_103);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
x_112 = l_Lean_Parser_isEOI(x_107);
if (x_112 == 0)
{
uint8_t x_113; 
x_113 = l_Lean_Parser_isExitCommand(x_107);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = l_Lean_Elab_Frontend_elabCommandAtFrontend(x_107, x_1, x_111);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_1);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
x_117 = 0;
x_118 = lean_box(x_117);
if (lean_is_scalar(x_116)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_116;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_115);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; 
x_120 = lean_ctor_get(x_114, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_114, 1);
lean_inc(x_121);
lean_dec(x_114);
x_122 = l___private_Init_Lean_Elab_Frontend_1__getCmdContext(x_1, x_121);
lean_dec(x_1);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_127 = x_123;
} else {
 lean_dec_ref(x_123);
 x_127 = lean_box(0);
}
x_128 = l_Lean_Elab_logElabException___at_Lean_Elab_Command_elabInitQuot___spec__1(x_120, x_124, x_125);
lean_dec(x_124);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_130 = x_128;
} else {
 lean_dec_ref(x_128);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_127;
}
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_126);
x_132 = 0;
x_133 = lean_box(x_132);
if (lean_is_scalar(x_130)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_130;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_131);
return x_134;
}
}
else
{
uint8_t x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_107);
lean_dec(x_1);
x_135 = 1;
x_136 = lean_box(x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_111);
return x_137;
}
}
else
{
uint8_t x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_107);
lean_dec(x_1);
x_138 = 1;
x_139 = lean_box(x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_111);
return x_140;
}
}
}
}
lean_object* l_Lean_Elab_Frontend_processCommandsAux___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
lean_inc(x_1);
x_3 = l_Lean_Elab_Frontend_processCommand(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_2 = x_6;
goto _start;
}
else
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_3, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
}
lean_object* l_Lean_Elab_Frontend_processCommandsAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Frontend_processCommandsAux___main___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Frontend_processCommandsAux___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Frontend_processCommandsAux___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Frontend_processCommandsAux___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Frontend_processCommandsAux___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Frontend_processCommandsAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Frontend_processCommandsAux___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Frontend_processCommandsAux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Frontend_processCommandsAux(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Frontend_processCommands(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Frontend_processCommandsAux___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_process(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_14; lean_object* x_15; 
x_5 = lean_box(0);
lean_inc(x_2);
x_6 = l_Lean_Elab_Command_mkState(x_2, x_5, x_3);
x_14 = l_Lean_Parser_ModuleParserState_inhabited___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_Elab_parseImports___closed__1;
x_17 = l_Lean_Parser_mkParserContextCore(x_2, x_1, x_16);
lean_dec(x_2);
x_18 = l_Lean_Elab_Frontend_processCommandsAux___main___rarg(x_17, x_15);
x_7 = x_18;
goto block_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
lean_dec(x_4);
x_20 = l_Lean_Parser_mkParserContextCore(x_2, x_1, x_19);
lean_dec(x_2);
x_21 = l_Lean_Elab_Frontend_processCommandsAux___main___rarg(x_20, x_15);
x_7 = x_21;
goto block_13;
}
block_13:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
lean_object* l_Lean_Elab_testFrontend(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = lean_mk_empty_environment(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_53; 
x_53 = l_Lean_Elab_parseImports___closed__1;
x_9 = x_53;
goto block_52;
}
else
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_3, 0);
lean_inc(x_54);
lean_dec(x_3);
x_9 = x_54;
goto block_52;
}
block_52:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_Lean_Parser_mkParserContextCore(x_7, x_1, x_9);
lean_inc(x_10);
x_11 = l_Lean_Parser_parseHeader(x_7, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Elab_processHeader(x_13, x_15, x_10, x_5, x_8);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
x_22 = l_Lean_Elab_Command_mkState(x_20, x_21, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_14);
x_24 = l_Lean_Elab_Frontend_processCommandsAux___main___rarg(x_10, x_23);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_ctor_set(x_17, 1, x_30);
lean_ctor_set(x_17, 0, x_29);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 0, x_17);
return x_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_dec(x_24);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_ctor_set(x_17, 1, x_34);
lean_ctor_set(x_17, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_17);
lean_ctor_set(x_35, 1, x_18);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_36 = lean_ctor_get(x_17, 0);
x_37 = lean_ctor_get(x_17, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_17);
x_38 = l_Lean_Elab_Command_mkState(x_36, x_37, x_2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_14);
x_40 = l_Lean_Elab_Frontend_processCommandsAux___main___rarg(x_10, x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
if (lean_is_scalar(x_42)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_42;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_18);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_16);
if (x_48 == 0)
{
return x_16;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_16, 0);
x_50 = lean_ctor_get(x_16, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_16);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_6);
if (x_55 == 0)
{
return x_6;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_6, 0);
x_57 = lean_ctor_get(x_6, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_6);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
lean_object* initialize_Init_Lean_Elab_Import(lean_object*);
lean_object* initialize_Init_Lean_Elab_Command(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_Frontend(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Elab_Import(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
