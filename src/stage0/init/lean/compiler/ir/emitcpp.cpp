// Lean compiler output
// Module: init.lean.compiler.ir.emitcpp
// Imports: init.control.conditional init.lean.name_mangling init.lean.compiler.ir.compilerm init.lean.compiler.ir.emitutil
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__24;
extern obj* l_Lean_IR_getDecl___closed__1;
obj* l_Lean_IR_EmitCpp_leanMainFn;
obj* l_Lean_IR_EmitCpp_emit(obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_IR_EmitCpp_emit___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__15;
extern obj* l_Array_empty___closed__1;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__16;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__14;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__1;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__8;
obj* l_Lean_IR_EmitCpp_emit___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_name__mangling_2__Name_mangleAux___main(obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__11;
obj* l_Lean_PersistentEnvExtension_getEntries___rarg(obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__13;
obj* l_Lean_IR_EmitCpp_emitLn___boxed(obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
uint8 l_List_foldr___main___at_Lean_IR_EmitCpp_main___spec__1(uint8, obj*);
obj* l_Lean_IR_EmitCpp_emitLn___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_emitCpp___closed__1;
obj* l_Lean_IR_usesLeanNamespace___main(obj*, obj*);
obj* l_Lean_IR_EmitCpp_emit___boxed(obj*);
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__6;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__7;
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_IR_EmitCpp_getDecl(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitLn(obj*);
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__17;
obj* l_Lean_IR_EmitCpp_emitMainFn(obj*, obj*);
extern obj* l_Char_HasRepr___closed__1;
extern obj* l_Lean_IR_declMapExt;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_IR_Decl_name___main(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__20;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__12;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__2;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__3;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__4;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__26;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__21;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__23;
obj* l_List_foldr___main___at_Lean_IR_EmitCpp_main___spec__1___boxed(obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__22;
obj* l_Lean_IR_EmitCpp_main(obj*, obj*);
obj* l_Lean_IR_findEnvDecl(obj*, obj*);
obj* l_Lean_IR_EmitCpp_getModName(obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitLn___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__5;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__27;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__29;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__19;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__28;
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__25;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__10;
namespace lean {
namespace ir {
obj* emit_cpp_core(obj*, obj*);
}}
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__9;
extern obj* l_IO_println___rarg___closed__1;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__18;
obj* l_Lean_IR_EmitCpp_getEnv(obj*, obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* _init_l_Lean_IR_EmitCpp_leanMainFn() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_lean_main");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_getEnv(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_4 = x_1;
} else {
 lean::inc(x_2);
 lean::dec(x_1);
 x_4 = lean::box(0);
}
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
if (lean::is_scalar(x_4)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_4;
}
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_2);
return x_8;
}
}
obj* l_Lean_IR_EmitCpp_getModName(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_4 = x_1;
} else {
 lean::inc(x_2);
 lean::dec(x_1);
 x_4 = lean::box(0);
}
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
if (lean::is_scalar(x_4)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_4;
}
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_2);
return x_8;
}
}
obj* l_Lean_IR_EmitCpp_getDecl(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_getEnv(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_set(x_3, 1, lean::box(0));
 x_8 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = l_Lean_IR_findEnvDecl(x_4, x_0);
lean::dec(x_4);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
x_11 = l_Lean_Name_toString___closed__1;
x_12 = l_Lean_Name_toStringWithSep___main(x_11, x_0);
x_13 = l_Lean_IR_getDecl___closed__1;
x_14 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_16 = l_Char_HasRepr___closed__1;
x_17 = lean::string_append(x_14, x_16);
if (lean::is_scalar(x_8)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_8;
 lean::cnstr_set_tag(x_8, 1);
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_6);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_9, 0);
lean::inc(x_20);
lean::dec(x_9);
if (lean::is_scalar(x_8)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_8;
}
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_6);
return x_23;
}
}
else
{
obj* x_25; obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_0);
x_25 = lean::cnstr_get(x_3, 0);
x_27 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_29 = x_3;
} else {
 lean::inc(x_25);
 lean::inc(x_27);
 lean::dec(x_3);
 x_29 = lean::box(0);
}
if (lean::is_scalar(x_29)) {
 x_30 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_30 = x_29;
}
lean::cnstr_set(x_30, 0, x_25);
lean::cnstr_set(x_30, 1, x_27);
return x_30;
}
}
}
obj* l_Lean_IR_EmitCpp_emit___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_6 = x_3;
} else {
 lean::inc(x_4);
 lean::dec(x_3);
 x_6 = lean::box(0);
}
x_7 = lean::apply_1(x_0, x_1);
x_8 = lean::string_append(x_4, x_7);
lean::dec(x_7);
x_10 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_11 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_11 = x_6;
}
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_8);
return x_11;
}
}
obj* l_Lean_IR_EmitCpp_emit(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_EmitCpp_emit___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_Lean_IR_EmitCpp_emit___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_EmitCpp_emit___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_IR_EmitCpp_emit___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_EmitCpp_emit(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_EmitCpp_emitLn___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_6 = x_3;
} else {
 lean::inc(x_4);
 lean::dec(x_3);
 x_6 = lean::box(0);
}
x_7 = lean::apply_1(x_0, x_1);
x_8 = lean::string_append(x_4, x_7);
lean::dec(x_7);
x_10 = l_IO_println___rarg___closed__1;
x_11 = lean::string_append(x_8, x_10);
x_12 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_6;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
return x_13;
}
}
obj* l_Lean_IR_EmitCpp_emitLn(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_EmitCpp_emitLn___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_Lean_IR_EmitCpp_emitLn___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_EmitCpp_emitLn___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_IR_EmitCpp_emitLn___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_EmitCpp_emitLn(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("}");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("if (io_result_is_ok(w)) {");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("  int ret = lean::unbox(io_result_get_value(w));");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("  lean::dec_ref(w);");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("  return ret;");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("} else {");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__7() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("  lean::io_result_show_error(w);");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__8() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("  return 1;");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__9() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("main");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__10() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid main function, incorrect arity when generating code");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__11() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("obj * w = lean::io_mk_world();");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__12() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("w = initialize_");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__13() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("(w);");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__14() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::io_mark_end_initialization();");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__15() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("if (io_result_is_ok(w)) {\n");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__16() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::scoped_task_manager tmanager(lean::hardware_concurrency());");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__17() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::mk_string("w = ");
x_1 = l_Lean_IR_EmitCpp_leanMainFn;
x_2 = lean::string_append(x_0, x_1);
x_3 = lean::mk_string("(w);");
x_4 = lean::string_append(x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__18() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("int main(int argc, char ** argv) {");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__19() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::initialize_runtime_module();");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__20() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("namespace lean { void initialize(); }");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__21() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::initialize();");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__22() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("obj* in = lean::box(0);");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__23() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("int i = argc;\n");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__24() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("while (i > 1) {");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__25() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" i--;");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__26() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" obj* n = lean::alloc_cnstr(1,2,0); lean::cnstr_set(n, 0, lean::mk_string(argv[i])); lean::cnstr_set(n, 1, in);");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__27() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" in = n;");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__28() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::mk_string("w = ");
x_1 = l_Lean_IR_EmitCpp_leanMainFn;
x_2 = lean::string_append(x_0, x_1);
x_3 = lean::mk_string("(in, w);");
x_4 = lean::string_append(x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__29() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("function declaration expected");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitMainFn(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; 
x_4 = l_Lean_IR_EmitCpp_emitMainFn___closed__9;
lean::inc(x_0);
x_6 = l_Lean_IR_EmitCpp_getDecl(x_4, x_0, x_1);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_set(x_6, 1, lean::box(0));
 x_11 = x_6;
} else {
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
x_14 = lean::array_get_size(x_12);
lean::dec(x_12);
x_16 = lean::mk_nat_obj(2ul);
x_17 = lean::nat_dec_eq(x_14, x_16);
if (x_17 == 0)
{
obj* x_18; uint8 x_19; 
x_18 = lean::mk_nat_obj(1ul);
x_19 = lean::nat_dec_eq(x_14, x_18);
lean::dec(x_14);
if (x_19 == 0)
{
obj* x_23; obj* x_24; 
lean::dec(x_7);
lean::dec(x_0);
x_23 = l_Lean_IR_EmitCpp_emitMainFn___closed__10;
if (lean::is_scalar(x_11)) {
 x_24 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_24 = x_11;
 lean::cnstr_set_tag(x_11, 1);
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_9);
return x_24;
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_30; 
x_25 = lean::box(0);
if (lean::is_scalar(x_11)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_11;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::inc(x_0);
x_30 = l_Lean_IR_EmitCpp_getEnv(x_0, x_26);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_33; obj* x_36; uint8 x_38; 
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
lean::dec(x_30);
x_36 = l_Lean_IR_usesLeanNamespace___main(x_31, x_7);
lean::dec(x_31);
x_38 = lean::unbox(x_36);
if (x_38 == 0)
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_39 = l_Lean_IR_EmitCpp_emitMainFn___closed__18;
x_40 = lean::string_append(x_33, x_39);
x_41 = l_IO_println___rarg___closed__1;
x_42 = lean::string_append(x_40, x_41);
x_43 = l_Lean_IR_EmitCpp_emitMainFn___closed__19;
x_44 = lean::string_append(x_42, x_43);
x_45 = lean::string_append(x_44, x_41);
x_27 = x_45;
goto lbl_28;
}
else
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_46 = l_Lean_IR_EmitCpp_emitMainFn___closed__20;
x_47 = lean::string_append(x_33, x_46);
x_48 = l_IO_println___rarg___closed__1;
x_49 = lean::string_append(x_47, x_48);
x_50 = l_Lean_IR_EmitCpp_emitMainFn___closed__18;
x_51 = lean::string_append(x_49, x_50);
x_52 = lean::string_append(x_51, x_48);
x_53 = l_Lean_IR_EmitCpp_emitMainFn___closed__21;
x_54 = lean::string_append(x_52, x_53);
x_55 = lean::string_append(x_54, x_48);
x_27 = x_55;
goto lbl_28;
}
}
else
{
obj* x_58; obj* x_60; obj* x_62; obj* x_63; 
lean::dec(x_7);
lean::dec(x_0);
x_58 = lean::cnstr_get(x_30, 0);
x_60 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 x_62 = x_30;
} else {
 lean::inc(x_58);
 lean::inc(x_60);
 lean::dec(x_30);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_58);
lean::cnstr_set(x_63, 1, x_60);
return x_63;
}
lbl_28:
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_64 = l_Lean_IR_EmitCpp_emitMainFn___closed__11;
x_65 = lean::string_append(x_27, x_64);
x_66 = l_IO_println___rarg___closed__1;
x_67 = lean::string_append(x_65, x_66);
x_68 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_68, 0, x_25);
lean::cnstr_set(x_68, 1, x_67);
x_69 = l_Lean_IR_EmitCpp_getModName(x_0, x_68);
if (lean::obj_tag(x_69) == 0)
{
obj* x_70; obj* x_72; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_80; obj* x_81; obj* x_82; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_69, 1);
lean::inc(x_72);
lean::dec(x_69);
x_75 = l_String_splitAux___main___closed__1;
x_76 = l___private_init_lean_name__mangling_2__Name_mangleAux___main(x_75, x_70);
x_77 = l_Lean_IR_EmitCpp_emitMainFn___closed__12;
x_78 = lean::string_append(x_77, x_76);
lean::dec(x_76);
x_80 = l_Lean_IR_EmitCpp_emitMainFn___closed__13;
x_81 = lean::string_append(x_78, x_80);
x_82 = lean::string_append(x_72, x_81);
lean::dec(x_81);
x_84 = lean::string_append(x_82, x_66);
x_85 = l_Lean_IR_EmitCpp_emitMainFn___closed__14;
x_86 = lean::string_append(x_84, x_85);
x_87 = lean::string_append(x_86, x_66);
x_88 = l_Lean_IR_EmitCpp_emitMainFn___closed__15;
x_89 = lean::string_append(x_87, x_88);
x_90 = lean::string_append(x_89, x_66);
x_91 = l_Lean_IR_EmitCpp_emitMainFn___closed__16;
x_92 = lean::string_append(x_90, x_91);
x_93 = lean::string_append(x_92, x_66);
x_94 = l_Lean_IR_EmitCpp_emitMainFn___closed__17;
x_95 = lean::string_append(x_93, x_94);
x_96 = lean::string_append(x_95, x_66);
x_2 = x_96;
goto lbl_3;
}
else
{
obj* x_97; obj* x_99; obj* x_101; obj* x_102; 
x_97 = lean::cnstr_get(x_69, 0);
x_99 = lean::cnstr_get(x_69, 1);
if (lean::is_exclusive(x_69)) {
 x_101 = x_69;
} else {
 lean::inc(x_97);
 lean::inc(x_99);
 lean::dec(x_69);
 x_101 = lean::box(0);
}
if (lean::is_scalar(x_101)) {
 x_102 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_102 = x_101;
}
lean::cnstr_set(x_102, 0, x_97);
lean::cnstr_set(x_102, 1, x_99);
return x_102;
}
}
}
}
else
{
obj* x_104; obj* x_105; obj* x_106; obj* x_109; 
lean::dec(x_14);
x_104 = lean::box(0);
if (lean::is_scalar(x_11)) {
 x_105 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_105 = x_11;
}
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_9);
lean::inc(x_0);
x_109 = l_Lean_IR_EmitCpp_getEnv(x_0, x_105);
if (lean::obj_tag(x_109) == 0)
{
obj* x_110; obj* x_112; obj* x_115; uint8 x_117; 
x_110 = lean::cnstr_get(x_109, 0);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_109, 1);
lean::inc(x_112);
lean::dec(x_109);
x_115 = l_Lean_IR_usesLeanNamespace___main(x_110, x_7);
lean::dec(x_110);
x_117 = lean::unbox(x_115);
if (x_117 == 0)
{
obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; 
x_118 = l_Lean_IR_EmitCpp_emitMainFn___closed__18;
x_119 = lean::string_append(x_112, x_118);
x_120 = l_IO_println___rarg___closed__1;
x_121 = lean::string_append(x_119, x_120);
x_122 = l_Lean_IR_EmitCpp_emitMainFn___closed__19;
x_123 = lean::string_append(x_121, x_122);
x_124 = lean::string_append(x_123, x_120);
x_106 = x_124;
goto lbl_107;
}
else
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
x_125 = l_Lean_IR_EmitCpp_emitMainFn___closed__20;
x_126 = lean::string_append(x_112, x_125);
x_127 = l_IO_println___rarg___closed__1;
x_128 = lean::string_append(x_126, x_127);
x_129 = l_Lean_IR_EmitCpp_emitMainFn___closed__18;
x_130 = lean::string_append(x_128, x_129);
x_131 = lean::string_append(x_130, x_127);
x_132 = l_Lean_IR_EmitCpp_emitMainFn___closed__21;
x_133 = lean::string_append(x_131, x_132);
x_134 = lean::string_append(x_133, x_127);
x_106 = x_134;
goto lbl_107;
}
}
else
{
obj* x_137; obj* x_139; obj* x_141; obj* x_142; 
lean::dec(x_7);
lean::dec(x_0);
x_137 = lean::cnstr_get(x_109, 0);
x_139 = lean::cnstr_get(x_109, 1);
if (lean::is_exclusive(x_109)) {
 x_141 = x_109;
} else {
 lean::inc(x_137);
 lean::inc(x_139);
 lean::dec(x_109);
 x_141 = lean::box(0);
}
if (lean::is_scalar(x_141)) {
 x_142 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_142 = x_141;
}
lean::cnstr_set(x_142, 0, x_137);
lean::cnstr_set(x_142, 1, x_139);
return x_142;
}
lbl_107:
{
obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; 
x_143 = l_Lean_IR_EmitCpp_emitMainFn___closed__11;
x_144 = lean::string_append(x_106, x_143);
x_145 = l_IO_println___rarg___closed__1;
x_146 = lean::string_append(x_144, x_145);
x_147 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_147, 0, x_104);
lean::cnstr_set(x_147, 1, x_146);
x_148 = l_Lean_IR_EmitCpp_getModName(x_0, x_147);
if (lean::obj_tag(x_148) == 0)
{
obj* x_149; obj* x_151; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_159; obj* x_160; obj* x_161; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; 
x_149 = lean::cnstr_get(x_148, 0);
lean::inc(x_149);
x_151 = lean::cnstr_get(x_148, 1);
lean::inc(x_151);
lean::dec(x_148);
x_154 = l_String_splitAux___main___closed__1;
x_155 = l___private_init_lean_name__mangling_2__Name_mangleAux___main(x_154, x_149);
x_156 = l_Lean_IR_EmitCpp_emitMainFn___closed__12;
x_157 = lean::string_append(x_156, x_155);
lean::dec(x_155);
x_159 = l_Lean_IR_EmitCpp_emitMainFn___closed__13;
x_160 = lean::string_append(x_157, x_159);
x_161 = lean::string_append(x_151, x_160);
lean::dec(x_160);
x_163 = lean::string_append(x_161, x_145);
x_164 = l_Lean_IR_EmitCpp_emitMainFn___closed__14;
x_165 = lean::string_append(x_163, x_164);
x_166 = lean::string_append(x_165, x_145);
x_167 = l_Lean_IR_EmitCpp_emitMainFn___closed__15;
x_168 = lean::string_append(x_166, x_167);
x_169 = lean::string_append(x_168, x_145);
x_170 = l_Lean_IR_EmitCpp_emitMainFn___closed__16;
x_171 = lean::string_append(x_169, x_170);
x_172 = lean::string_append(x_171, x_145);
x_173 = l_Lean_IR_EmitCpp_emitMainFn___closed__22;
x_174 = lean::string_append(x_172, x_173);
x_175 = lean::string_append(x_174, x_145);
x_176 = l_Lean_IR_EmitCpp_emitMainFn___closed__23;
x_177 = lean::string_append(x_175, x_176);
x_178 = lean::string_append(x_177, x_145);
x_179 = l_Lean_IR_EmitCpp_emitMainFn___closed__24;
x_180 = lean::string_append(x_178, x_179);
x_181 = lean::string_append(x_180, x_145);
x_182 = l_Lean_IR_EmitCpp_emitMainFn___closed__25;
x_183 = lean::string_append(x_181, x_182);
x_184 = lean::string_append(x_183, x_145);
x_185 = l_Lean_IR_EmitCpp_emitMainFn___closed__26;
x_186 = lean::string_append(x_184, x_185);
x_187 = lean::string_append(x_186, x_145);
x_188 = l_Lean_IR_EmitCpp_emitMainFn___closed__27;
x_189 = lean::string_append(x_187, x_188);
x_190 = lean::string_append(x_189, x_145);
x_191 = l_Lean_IR_EmitCpp_emitMainFn___closed__1;
x_192 = lean::string_append(x_190, x_191);
x_193 = lean::string_append(x_192, x_145);
x_194 = l_Lean_IR_EmitCpp_emitMainFn___closed__28;
x_195 = lean::string_append(x_193, x_194);
x_196 = lean::string_append(x_195, x_145);
x_2 = x_196;
goto lbl_3;
}
else
{
obj* x_197; obj* x_199; obj* x_201; obj* x_202; 
x_197 = lean::cnstr_get(x_148, 0);
x_199 = lean::cnstr_get(x_148, 1);
if (lean::is_exclusive(x_148)) {
 x_201 = x_148;
} else {
 lean::inc(x_197);
 lean::inc(x_199);
 lean::dec(x_148);
 x_201 = lean::box(0);
}
if (lean::is_scalar(x_201)) {
 x_202 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_202 = x_201;
}
lean::cnstr_set(x_202, 0, x_197);
lean::cnstr_set(x_202, 1, x_199);
return x_202;
}
}
}
}
else
{
obj* x_205; obj* x_207; obj* x_208; obj* x_209; 
lean::dec(x_7);
lean::dec(x_0);
x_205 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_207 = x_6;
} else {
 lean::inc(x_205);
 lean::dec(x_6);
 x_207 = lean::box(0);
}
x_208 = l_Lean_IR_EmitCpp_emitMainFn___closed__29;
if (lean::is_scalar(x_207)) {
 x_209 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_209 = x_207;
 lean::cnstr_set_tag(x_207, 1);
}
lean::cnstr_set(x_209, 0, x_208);
lean::cnstr_set(x_209, 1, x_205);
return x_209;
}
}
else
{
obj* x_211; obj* x_213; obj* x_215; obj* x_216; 
lean::dec(x_0);
x_211 = lean::cnstr_get(x_6, 0);
x_213 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 x_215 = x_6;
} else {
 lean::inc(x_211);
 lean::inc(x_213);
 lean::dec(x_6);
 x_215 = lean::box(0);
}
if (lean::is_scalar(x_215)) {
 x_216 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_216 = x_215;
}
lean::cnstr_set(x_216, 0, x_211);
lean::cnstr_set(x_216, 1, x_213);
return x_216;
}
lbl_3:
{
obj* x_217; obj* x_218; obj* x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; 
x_217 = l_Lean_IR_EmitCpp_emitMainFn___closed__1;
x_218 = lean::string_append(x_2, x_217);
x_219 = l_IO_println___rarg___closed__1;
x_220 = lean::string_append(x_218, x_219);
x_221 = l_Lean_IR_EmitCpp_emitMainFn___closed__2;
x_222 = lean::string_append(x_220, x_221);
x_223 = lean::string_append(x_222, x_219);
x_224 = l_Lean_IR_EmitCpp_emitMainFn___closed__3;
x_225 = lean::string_append(x_223, x_224);
x_226 = lean::string_append(x_225, x_219);
x_227 = l_Lean_IR_EmitCpp_emitMainFn___closed__4;
x_228 = lean::string_append(x_226, x_227);
x_229 = lean::string_append(x_228, x_219);
x_230 = l_Lean_IR_EmitCpp_emitMainFn___closed__5;
x_231 = lean::string_append(x_229, x_230);
x_232 = lean::string_append(x_231, x_219);
x_233 = l_Lean_IR_EmitCpp_emitMainFn___closed__6;
x_234 = lean::string_append(x_232, x_233);
x_235 = lean::string_append(x_234, x_219);
x_236 = l_Lean_IR_EmitCpp_emitMainFn___closed__7;
x_237 = lean::string_append(x_235, x_236);
x_238 = lean::string_append(x_237, x_219);
x_239 = lean::string_append(x_238, x_227);
x_240 = lean::string_append(x_239, x_219);
x_241 = l_Lean_IR_EmitCpp_emitMainFn___closed__8;
x_242 = lean::string_append(x_240, x_241);
x_243 = lean::string_append(x_242, x_219);
x_244 = lean::string_append(x_243, x_217);
x_245 = lean::string_append(x_244, x_219);
x_246 = lean::string_append(x_245, x_217);
x_247 = lean::string_append(x_246, x_219);
x_248 = lean::box(0);
x_249 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_249, 0, x_248);
lean::cnstr_set(x_249, 1, x_247);
return x_249;
}
}
}
uint8 l_List_foldr___main___at_Lean_IR_EmitCpp_main___spec__1(uint8 x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_3; uint8 x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = l_List_foldr___main___at_Lean_IR_EmitCpp_main___spec__1(x_0, x_3);
x_5 = l_Lean_IR_Decl_name___main(x_2);
x_6 = l_Lean_IR_EmitCpp_emitMainFn___closed__9;
x_7 = lean_name_dec_eq(x_5, x_6);
lean::dec(x_5);
if (x_7 == 0)
{
return x_4;
}
else
{
uint8 x_9; 
x_9 = 1;
return x_9;
}
}
}
}
obj* l_Lean_IR_EmitCpp_main(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; 
lean::inc(x_0);
x_3 = l_Lean_IR_EmitCpp_getEnv(x_0, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; uint8 x_15; uint8 x_16; 
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_8 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = lean::box(0);
lean::inc(x_6);
if (lean::is_scalar(x_8)) {
 x_11 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_11 = x_8;
}
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_6);
x_12 = l_Lean_IR_declMapExt;
x_13 = l_Lean_PersistentEnvExtension_getEntries___rarg(x_12, x_4);
lean::dec(x_4);
x_15 = 0;
x_16 = l_List_foldr___main___at_Lean_IR_EmitCpp_main___spec__1(x_15, x_13);
lean::dec(x_13);
if (x_16 == 0)
{
obj* x_20; 
lean::dec(x_0);
lean::dec(x_11);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_9);
lean::cnstr_set(x_20, 1, x_6);
return x_20;
}
else
{
obj* x_22; 
lean::dec(x_6);
x_22 = l_Lean_IR_EmitCpp_emitMainFn(x_0, x_11);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_25; obj* x_26; 
x_23 = lean::cnstr_get(x_22, 1);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 0);
 x_25 = x_22;
} else {
 lean::inc(x_23);
 lean::dec(x_22);
 x_25 = lean::box(0);
}
if (lean::is_scalar(x_25)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_25;
}
lean::cnstr_set(x_26, 0, x_9);
lean::cnstr_set(x_26, 1, x_23);
return x_26;
}
else
{
obj* x_27; obj* x_29; obj* x_31; obj* x_32; 
x_27 = lean::cnstr_get(x_22, 0);
x_29 = lean::cnstr_get(x_22, 1);
if (lean::is_exclusive(x_22)) {
 x_31 = x_22;
} else {
 lean::inc(x_27);
 lean::inc(x_29);
 lean::dec(x_22);
 x_31 = lean::box(0);
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_27);
lean::cnstr_set(x_32, 1, x_29);
return x_32;
}
}
}
else
{
obj* x_34; obj* x_36; obj* x_38; obj* x_39; 
lean::dec(x_0);
x_34 = lean::cnstr_get(x_3, 0);
x_36 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_38 = x_3;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_3);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_34);
lean::cnstr_set(x_39, 1, x_36);
return x_39;
}
}
}
obj* l_List_foldr___main___at_Lean_IR_EmitCpp_main___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = l_List_foldr___main___at_Lean_IR_EmitCpp_main___spec__1(x_2, x_1);
x_4 = lean::box(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_IR_emitCpp___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("");
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
namespace lean {
namespace ir {
obj* emit_cpp_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::box(0);
x_3 = lean::box(0);
x_4 = l_Array_empty___closed__1;
x_5 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_1);
lean::cnstr_set(x_5, 3, x_3);
lean::cnstr_set(x_5, 4, x_4);
x_6 = l_Lean_IR_emitCpp___closed__1;
x_7 = l_Lean_IR_EmitCpp_main(x_5, x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_8);
return x_11;
}
else
{
obj* x_12; obj* x_15; 
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
lean::dec(x_7);
x_15 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_15, 0, x_12);
return x_15;
}
}
}
}}
obj* initialize_init_control_conditional(obj*);
obj* initialize_init_lean_name__mangling(obj*);
obj* initialize_init_lean_compiler_ir_compilerm(obj*);
obj* initialize_init_lean_compiler_ir_emitutil(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_emitcpp(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_control_conditional(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_name__mangling(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_compilerm(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_emitutil(w);
if (io_result_is_error(w)) return w;
 l_Lean_IR_EmitCpp_leanMainFn = _init_l_Lean_IR_EmitCpp_leanMainFn();
lean::mark_persistent(l_Lean_IR_EmitCpp_leanMainFn);
 l_Lean_IR_EmitCpp_emitMainFn___closed__1 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__1);
 l_Lean_IR_EmitCpp_emitMainFn___closed__2 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__2();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__2);
 l_Lean_IR_EmitCpp_emitMainFn___closed__3 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__3();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__3);
 l_Lean_IR_EmitCpp_emitMainFn___closed__4 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__4();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__4);
 l_Lean_IR_EmitCpp_emitMainFn___closed__5 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__5();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__5);
 l_Lean_IR_EmitCpp_emitMainFn___closed__6 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__6();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__6);
 l_Lean_IR_EmitCpp_emitMainFn___closed__7 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__7();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__7);
 l_Lean_IR_EmitCpp_emitMainFn___closed__8 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__8();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__8);
 l_Lean_IR_EmitCpp_emitMainFn___closed__9 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__9();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__9);
 l_Lean_IR_EmitCpp_emitMainFn___closed__10 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__10();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__10);
 l_Lean_IR_EmitCpp_emitMainFn___closed__11 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__11();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__11);
 l_Lean_IR_EmitCpp_emitMainFn___closed__12 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__12();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__12);
 l_Lean_IR_EmitCpp_emitMainFn___closed__13 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__13();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__13);
 l_Lean_IR_EmitCpp_emitMainFn___closed__14 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__14();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__14);
 l_Lean_IR_EmitCpp_emitMainFn___closed__15 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__15();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__15);
 l_Lean_IR_EmitCpp_emitMainFn___closed__16 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__16();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__16);
 l_Lean_IR_EmitCpp_emitMainFn___closed__17 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__17();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__17);
 l_Lean_IR_EmitCpp_emitMainFn___closed__18 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__18();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__18);
 l_Lean_IR_EmitCpp_emitMainFn___closed__19 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__19();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__19);
 l_Lean_IR_EmitCpp_emitMainFn___closed__20 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__20();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__20);
 l_Lean_IR_EmitCpp_emitMainFn___closed__21 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__21();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__21);
 l_Lean_IR_EmitCpp_emitMainFn___closed__22 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__22();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__22);
 l_Lean_IR_EmitCpp_emitMainFn___closed__23 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__23();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__23);
 l_Lean_IR_EmitCpp_emitMainFn___closed__24 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__24();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__24);
 l_Lean_IR_EmitCpp_emitMainFn___closed__25 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__25();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__25);
 l_Lean_IR_EmitCpp_emitMainFn___closed__26 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__26();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__26);
 l_Lean_IR_EmitCpp_emitMainFn___closed__27 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__27();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__27);
 l_Lean_IR_EmitCpp_emitMainFn___closed__28 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__28();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__28);
 l_Lean_IR_EmitCpp_emitMainFn___closed__29 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__29();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__29);
 l_Lean_IR_emitCpp___closed__1 = _init_l_Lean_IR_emitCpp___closed__1();
lean::mark_persistent(l_Lean_IR_emitCpp___closed__1);
return w;
}
