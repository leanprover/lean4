// Lean compiler output
// Module: init.lean.compiler.ir.compilerm
// Imports: init.control.reader init.lean.environment init.lean.compiler.ir.basic init.lean.compiler.ir.format
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
obj* l_Lean_IR_getDecl___closed__1;
obj* l_Lean_IR_getDecl___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_logMessageIf___boxed(obj*);
obj* l___private_init_lean_compiler_ir_compilerm_1__isLogEnabledFor___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_LogEntry_fmt___main___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_setBlack___main___rarg(obj*);
obj* l_Lean_IR_declMapExt___elambda__2___rarg___boxed(obj*, obj*);
obj* l_Lean_IR_logMessage___rarg(obj*, obj*, obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_IR_findDecl_x_27(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_containsDecl(obj*, obj*, obj*);
obj* l_Lean_IR_LogEntry_fmt___main(obj*);
obj* l_Lean_IR_findEnvDecl___boxed(obj*, obj*);
extern obj* l_Array_empty___closed__1;
obj* l_Lean_IR_logMessage___boxed(obj*);
obj* l_Lean_Format_pretty(obj*, obj*);
obj* l_Lean_IR_mkDeclMapExtension___closed__1;
extern obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
obj* l___private_init_lean_compiler_ir_compilerm_3__logMessageIfAux___boxed(obj*);
obj* l_Lean_IR_formatDecl___main(obj*, obj*);
obj* l_Array_mfindAux___main___at_Lean_IR_findDeclAux_x_27___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__10(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_getEnv___boxed(obj*);
obj* l_HashMapImp_find___at_Lean_IR_findEnvDecl___spec__3(obj*, obj*);
obj* l_Lean_Format_group___main(obj*);
uint8 l_Array_anyMAux___main___at_Lean_IR_mkDeclMapExtension___spec__7(obj*, obj*, obj*);
obj* l_HashMapImp_contains___at_Lean_IR_containsDecl___spec__2___boxed(obj*, obj*);
obj* l_Lean_IR_findDeclAux_x_27___boxed(obj*, obj*, obj*);
obj* l_Lean_KVMap_findCore___main(obj*, obj*);
obj* l_HashMapImp_insert___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__2(obj*, obj*, obj*);
obj* l_Lean_PersistentEnvExtension_getEntries___rarg(obj*, obj*);
obj* l_mkHashMap___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__1(obj*);
obj* l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Log_format(obj*);
obj* l_Lean_IR_logMessage___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_AssocList_foldl___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__6(obj*, obj*);
obj* l_Lean_IR_findDecl(obj*, obj*, obj*);
obj* l_List_toArrayAux___main___rarg(obj*, obj*);
obj* l_Lean_IR_logMessageIf(obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
extern obj* l_Lean_Format_sbracket___closed__1;
obj* l_Array_miterateAux___main___at_Lean_IR_LogEntry_fmt___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_List_redLength___main___rarg(obj*);
obj* l_Lean_IR_addDecls___boxed(obj*, obj*, obj*);
extern obj* l_Lean_Options_empty;
obj* l_Lean_SMap_find___main___at_Lean_IR_findEnvDecl___spec__1(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Log_format___spec__1(obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_IR_findEnvDecl___spec__2(obj*, obj*);
uint8 l_Lean_SMap_contains___main___at_Lean_IR_containsDecl___spec__1(obj*, obj*);
obj* l_Array_mfindAux___main___at_Lean_IR_findDeclAux_x_27___spec__1(obj*, obj*, obj*);
obj* l_HashMapImp_expand___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__4(obj*, obj*);
obj* l_Lean_IR_getDecls___boxed(obj*);
extern obj* l___private_init_lean_environment_9__persistentEnvExtensionsRef;
uint8 l_Lean_KVMap_getBool(obj*, obj*, uint8);
extern obj* l_Lean_Format_sbracket___closed__2;
obj* l_Lean_IR_addDecl___boxed(obj*, obj*, obj*);
obj* l_Lean_SMap_insert___main___at_Lean_IR_mkDeclMapExtension___spec__3(obj*, obj*, obj*);
obj* l_Lean_registerEnvExtensionUnsafe___rarg(obj*, obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_mkDeclMapExtension___spec__6(obj*, obj*);
obj* l_Lean_IR_log(obj*, obj*, obj*);
obj* l_Lean_IR_mkDeclMapExtension(obj*);
obj* l_Lean_IR_tracePrefixOptionName;
obj* l_Array_anyMAux___main___at_Lean_IR_containsDecl_x_27___spec__1___boxed(obj*, obj*, obj*);
extern "C" usize lean_name_hash_usize(obj*);
extern obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
obj* l_Lean_PersistentEnvExtension_getState___rarg(obj*, obj*);
obj* l_HashMapImp_moveEntries___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__5(obj*, obj*, obj*);
obj* l_Lean_SMap_contains___main___at_Lean_IR_containsDecl___spec__1___boxed(obj*, obj*);
obj* l_HashMapImp_find___at_Lean_IR_findEnvDecl___spec__3___boxed(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Array_anyMAux___main___at_Lean_IR_mkDeclMapExtension___spec__7___boxed(obj*, obj*, obj*);
obj* l_Lean_SMap_switch___at_Lean_IR_mkDeclMapExtension___spec__2(obj*);
obj* l___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___closed__1;
obj* l_Lean_IR_addDecls(obj*, obj*, obj*);
namespace lean {
namespace ir {
obj* log_to_string_core(obj*);
}}
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__10___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_logDecls(obj*, obj*, obj*, obj*);
extern obj* l_Char_HasRepr___closed__1;
namespace lean {
namespace ir {
obj* add_decl_core(obj*, obj*);
}}
obj* l_Lean_SMap_empty___at_Lean_IR_mkDeclMapExtension___spec__1;
obj* l_Lean_IR_declMapExt;
obj* l_AssocList_contains___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__3___boxed(obj*, obj*);
obj* l_AssocList_foldl___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__9(obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_IR_Decl_name___main(obj*);
obj* l_Lean_IR_declMapExt___elambda__2(uint8);
obj* l_Lean_IR_LogEntry_Lean_HasFormat;
obj* l_Lean_IR_findDecl___boxed(obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_IR_mkDeclMapExtension___lambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_logMessage(obj*);
obj* l___private_init_lean_compiler_ir_compilerm_3__logMessageIfAux(obj*);
uint8 l_RBNode_isRed___main___rarg(obj*);
obj* l_Lean_IR_LogEntry_fmt(obj*);
obj* l___private_init_lean_compiler_ir_compilerm_3__logMessageIfAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
uint8 l_AssocList_contains___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__3(obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(obj*, obj*, obj*, obj*);
uint8 l___private_init_lean_compiler_ir_compilerm_1__isLogEnabledFor(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_IR_mkDeclMapExtension___spec__5(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Log_format___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_declMapExt___elambda__1(obj*);
extern obj* l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__2;
obj* l_Lean_IR_getDecl_x_27(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_compilerm_4__mkEntryArray(obj*);
obj* l_AssocList_replace___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__7(obj*, obj*, obj*);
extern obj* l_Lean_Format_sbracket___closed__3;
obj* l_Lean_IR_getDecl(obj*, obj*, obj*);
obj* l_Lean_PersistentEnvExtension_addEntry___rarg(obj*, obj*, obj*);
uint8 l_Lean_Name_quickLt(obj*, obj*);
obj* l_Lean_IR_findEnvDecl(obj*, obj*);
namespace lean {
usize usize_modn(usize, obj*);
}
obj* l_AssocList_find___main___at_Lean_IR_findEnvDecl___spec__4___boxed(obj*, obj*);
obj* l_Lean_SMap_find___main___at_Lean_IR_findEnvDecl___spec__1___boxed(obj*, obj*);
obj* l_Lean_IR_getEnv___rarg(obj*);
obj* l_Lean_IR_getDecl_x_27___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_mkHashMapImp___rarg(obj*);
obj* l_Lean_IR_modifyEnv(obj*, obj*, obj*);
obj* l_AssocList_find___main___at_Lean_IR_findEnvDecl___spec__4(obj*, obj*);
obj* l_Lean_IR_containsDecl_x_27(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_containsDecl___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_compilerm_3__logMessageIfAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_getEnv(obj*);
uint8 l_HashMapImp_contains___at_Lean_IR_containsDecl___spec__2(obj*, obj*);
obj* l_Lean_IR_declMapExt___elambda__2___rarg(obj*, obj*);
extern obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
obj* l_Lean_IR_Log_format___boxed(obj*);
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_IR_log___boxed(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_RBNode_find___main___at_Lean_IR_findEnvDecl___spec__2___boxed(obj*, obj*);
obj* l_Lean_IR_logMessageIf___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_declMapExt___elambda__2___boxed(obj*);
obj* l_List_foldl___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__8___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_findDeclAux_x_27(obj*, obj*, obj*);
obj* l_Lean_IR_findDecl_x_27___boxed(obj*, obj*, obj*, obj*);
uint8 l_Array_anyMAux___main___at_Lean_IR_containsDecl_x_27___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_addDecl(obj*, obj*, obj*);
obj* l_Lean_Name_append___main(obj*, obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_Lean_IR_modifyEnv___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_mkDeclMapExtension___lambda__1(uint8, obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__8(obj*, obj*, obj*);
obj* l_Lean_IR_containsDecl_x_27___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_IR_mkDeclMapExtension___spec__4(obj*, obj*, obj*);
obj* l_Lean_IR_getDecls(obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_LogEntry_fmt___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = 0;
x_10 = lean::box(1);
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_3);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_9);
x_12 = x_11;
x_13 = lean::mk_nat_obj(2ul);
x_14 = l_Lean_IR_formatDecl___main(x_13, x_8);
x_15 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_14);
lean::cnstr_set_scalar(x_15, sizeof(void*)*2, x_9);
x_16 = x_15;
x_17 = lean::mk_nat_obj(1ul);
x_18 = lean::nat_add(x_2, x_17);
lean::dec(x_2);
x_2 = x_18;
x_3 = x_16;
goto _start;
}
}
}
obj* l_Lean_IR_LogEntry_fmt___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_1);
x_8 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = 0;
x_10 = l_Lean_Format_sbracket___closed__1;
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_8);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_9);
x_12 = x_11;
x_13 = l_Lean_Format_sbracket___closed__2;
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_9);
x_15 = x_14;
x_16 = l_Lean_Format_sbracket___closed__3;
x_17 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_15);
x_18 = l_Lean_Format_group___main(x_17);
x_19 = lean::mk_nat_obj(0ul);
x_20 = lean::box(0);
x_21 = l_Array_miterateAux___main___at_Lean_IR_LogEntry_fmt___main___spec__1(x_3, x_3, x_19, x_20);
lean::dec(x_3);
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_18);
lean::cnstr_set(x_23, 1, x_21);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_9);
x_24 = x_23;
return x_24;
}
else
{
obj* x_25; 
x_25 = lean::cnstr_get(x_0, 0);
lean::inc(x_25);
lean::dec(x_0);
return x_25;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_LogEntry_fmt___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_Lean_IR_LogEntry_fmt___main___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_LogEntry_fmt(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_LogEntry_fmt___main(x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_LogEntry_Lean_HasFormat() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_LogEntry_fmt), 1, 0);
return x_0;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_Log_format___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = 0;
x_10 = lean::box(1);
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_3);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_9);
x_12 = x_11;
x_13 = l_Lean_IR_LogEntry_fmt___main(x_8);
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_9);
x_15 = x_14;
x_16 = lean::mk_nat_obj(1ul);
x_17 = lean::nat_add(x_2, x_16);
lean::dec(x_2);
x_2 = x_17;
x_3 = x_15;
goto _start;
}
}
}
obj* l_Lean_IR_Log_format(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(0ul);
x_2 = lean::box(0);
x_3 = l_Array_miterateAux___main___at_Lean_IR_Log_format___spec__1(x_0, x_0, x_1, x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_Log_format___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_Lean_IR_Log_format___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_Log_format___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_Log_format(x_0);
lean::dec(x_0);
return x_1;
}
}
namespace lean {
namespace ir {
obj* log_to_string_core(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_1 = lean::mk_nat_obj(0ul);
x_2 = lean::box(0);
x_3 = l_Array_miterateAux___main___at_Lean_IR_Log_format___spec__1(x_0, x_0, x_1, x_2);
lean::dec(x_0);
x_5 = l_Lean_Options_empty;
x_6 = l_Lean_Format_pretty(x_3, x_5);
return x_6;
}
}
}}
obj* l_Lean_IR_log(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_10 = x_3;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
x_11 = lean::array_push(x_8, x_0);
if (lean::is_scalar(x_10)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_10;
}
lean::cnstr_set(x_12, 0, x_6);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::box(0);
if (lean::is_scalar(x_5)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_5;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
return x_14;
}
}
obj* l_Lean_IR_log___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_log(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_IR_tracePrefixOptionName() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("trace");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("compiler");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("ir");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
uint8 l___private_init_lean_compiler_ir_compilerm_1__isLogEnabledFor(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; 
lean::inc(x_0);
x_3 = l_Lean_KVMap_findCore___main(x_0, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; uint8 x_5; uint8 x_6; 
x_4 = l_Lean_IR_tracePrefixOptionName;
x_5 = 0;
x_6 = l_Lean_KVMap_getBool(x_0, x_4, x_5);
return x_6;
}
else
{
obj* x_7; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
lean::dec(x_3);
switch (lean::obj_tag(x_7)) {
case 1:
{
uint8 x_11; 
lean::dec(x_0);
x_11 = lean::cnstr_get_scalar<uint8>(x_7, 0);
lean::dec(x_7);
return x_11;
}
default:
{
obj* x_14; uint8 x_15; uint8 x_16; 
lean::dec(x_7);
x_14 = l_Lean_IR_tracePrefixOptionName;
x_15 = 0;
x_16 = l_Lean_KVMap_getBool(x_0, x_14, x_15);
return x_16;
}
}
}
}
}
obj* l___private_init_lean_compiler_ir_compilerm_1__isLogEnabledFor___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l___private_init_lean_compiler_ir_compilerm_1__isLogEnabledFor(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_10; uint8 x_12; 
x_5 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_7 = x_4;
} else {
 lean::inc(x_5);
 lean::dec(x_4);
 x_7 = lean::box(0);
}
x_8 = lean::box(0);
lean::inc(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_5);
lean::inc(x_3);
x_12 = l___private_init_lean_compiler_ir_compilerm_1__isLogEnabledFor(x_3, x_0);
if (x_12 == 0)
{
obj* x_17; 
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_8);
lean::cnstr_set(x_17, 1, x_5);
return x_17;
}
else
{
obj* x_19; obj* x_20; 
lean::dec(x_5);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_1);
lean::cnstr_set(x_19, 1, x_2);
x_20 = l_Lean_IR_log(x_19, x_3, x_10);
lean::dec(x_3);
return x_20;
}
}
}
obj* l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l_Lean_IR_logDecls(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; 
x_4 = l_Lean_IR_tracePrefixOptionName;
lean::inc(x_0);
x_6 = l_Lean_Name_append___main(x_4, x_0);
x_7 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_6, x_0, x_1, x_2, x_3);
lean::dec(x_6);
return x_7;
}
}
obj* l___private_init_lean_compiler_ir_compilerm_3__logMessageIfAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_10; uint8 x_12; 
x_5 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_7 = x_4;
} else {
 lean::inc(x_5);
 lean::dec(x_4);
 x_7 = lean::box(0);
}
x_8 = lean::box(0);
lean::inc(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_5);
lean::inc(x_3);
x_12 = l___private_init_lean_compiler_ir_compilerm_1__isLogEnabledFor(x_3, x_1);
if (x_12 == 0)
{
obj* x_17; 
lean::dec(x_10);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_8);
lean::cnstr_set(x_17, 1, x_5);
return x_17;
}
else
{
obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_5);
x_19 = lean::apply_1(x_0, x_2);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
x_21 = l_Lean_IR_log(x_20, x_3, x_10);
lean::dec(x_3);
return x_21;
}
}
}
obj* l___private_init_lean_compiler_ir_compilerm_3__logMessageIfAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_compilerm_3__logMessageIfAux___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_compilerm_3__logMessageIfAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_compiler_ir_compilerm_3__logMessageIfAux___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_compilerm_3__logMessageIfAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_compilerm_3__logMessageIfAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_logMessageIf___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_IR_tracePrefixOptionName;
x_6 = l_Lean_Name_append___main(x_5, x_1);
x_7 = l___private_init_lean_compiler_ir_compilerm_3__logMessageIfAux___rarg(x_0, x_6, x_2, x_3, x_4);
lean::dec(x_6);
return x_7;
}
}
obj* l_Lean_IR_logMessageIf(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_logMessageIf___rarg), 5, 0);
return x_1;
}
}
obj* l_Lean_IR_logMessageIf___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_logMessageIf(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_logMessage___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_IR_tracePrefixOptionName;
x_6 = l___private_init_lean_compiler_ir_compilerm_3__logMessageIfAux___rarg(x_0, x_5, x_2, x_3, x_4);
return x_6;
}
}
obj* l_Lean_IR_logMessage(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_logMessage___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Lean_IR_logMessage___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_logMessage___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_logMessage___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_logMessage(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_modifyEnv(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_10 = x_3;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
x_11 = lean::apply_1(x_0, x_6);
if (lean::is_scalar(x_10)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_10;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_8);
x_13 = lean::box(0);
if (lean::is_scalar(x_5)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_5;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
return x_14;
}
}
obj* l_Lean_IR_modifyEnv___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_modifyEnv(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_mkHashMap___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_mkHashMapImp___rarg(x_0);
return x_1;
}
}
uint8 l_AssocList_contains___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__3(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
else
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 2);
x_5 = lean_name_dec_eq(x_3, x_0);
if (x_5 == 0)
{
x_1 = x_4;
goto _start;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
}
obj* l_AssocList_foldl___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__6(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; usize x_10; usize x_11; obj* x_13; obj* x_14; obj* x_15; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 x_8 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
x_9 = lean::array_get_size(x_0);
x_10 = lean_name_hash_usize(x_2);
x_11 = lean::usize_modn(x_10, x_9);
lean::dec(x_9);
x_13 = lean::array_uget(x_0, x_11);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(1, 3, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_2);
lean::cnstr_set(x_14, 1, x_4);
lean::cnstr_set(x_14, 2, x_13);
x_15 = lean::array_uset(x_0, x_11, x_14);
x_0 = x_15;
x_1 = x_6;
goto _start;
}
}
}
obj* l_HashMapImp_moveEntries___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_lt(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::array_fget(x_1, x_0);
x_9 = lean::box(0);
x_10 = lean::array_fset(x_1, x_0, x_9);
x_11 = l_AssocList_foldl___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__6(x_2, x_8);
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_0, x_12);
lean::dec(x_0);
x_0 = x_13;
x_1 = x_10;
x_2 = x_11;
goto _start;
}
}
}
obj* l_HashMapImp_expand___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::mk_nat_obj(2ul);
x_4 = lean::nat_mul(x_2, x_3);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = lean::mk_array(x_4, x_6);
x_8 = lean::mk_nat_obj(0ul);
x_9 = l_HashMapImp_moveEntries___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__5(x_8, x_1, x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_AssocList_replace___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; uint8 x_12; 
x_5 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
x_9 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 x_11 = x_2;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_2);
 x_11 = lean::box(0);
}
x_12 = lean_name_dec_eq(x_5, x_0);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = l_AssocList_replace___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__7(x_0, x_1, x_9);
if (lean::is_scalar(x_11)) {
 x_14 = lean::alloc_cnstr(1, 3, 0);
} else {
 x_14 = x_11;
}
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_7);
lean::cnstr_set(x_14, 2, x_13);
return x_14;
}
else
{
obj* x_17; 
lean::dec(x_7);
lean::dec(x_5);
if (lean::is_scalar(x_11)) {
 x_17 = lean::alloc_cnstr(1, 3, 0);
} else {
 x_17 = x_11;
}
lean::cnstr_set(x_17, 0, x_0);
lean::cnstr_set(x_17, 1, x_1);
lean::cnstr_set(x_17, 2, x_9);
return x_17;
}
}
}
}
obj* l_HashMapImp_insert___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; usize x_9; usize x_10; obj* x_11; uint8 x_12; 
x_3 = lean::cnstr_get(x_0, 0);
x_5 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_7 = x_0;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_0);
 x_7 = lean::box(0);
}
x_8 = lean::array_get_size(x_5);
x_9 = lean_name_hash_usize(x_1);
x_10 = lean::usize_modn(x_9, x_8);
x_11 = lean::array_uget(x_5, x_10);
x_12 = l_AssocList_contains___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__3(x_1, x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_16; obj* x_17; uint8 x_18; 
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_3, x_13);
lean::dec(x_3);
x_16 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_16, 0, x_1);
lean::cnstr_set(x_16, 1, x_2);
lean::cnstr_set(x_16, 2, x_11);
x_17 = lean::array_uset(x_5, x_10, x_16);
x_18 = lean::nat_dec_le(x_14, x_8);
lean::dec(x_8);
if (x_18 == 0)
{
obj* x_21; 
lean::dec(x_7);
x_21 = l_HashMapImp_expand___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__4(x_14, x_17);
return x_21;
}
else
{
obj* x_22; 
if (lean::is_scalar(x_7)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_7;
}
lean::cnstr_set(x_22, 0, x_14);
lean::cnstr_set(x_22, 1, x_17);
return x_22;
}
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_8);
x_24 = l_AssocList_replace___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__7(x_1, x_2, x_11);
x_25 = lean::array_uset(x_5, x_10, x_24);
if (lean::is_scalar(x_7)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_7;
}
lean::cnstr_set(x_26, 0, x_3);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
}
}
obj* l_List_foldl___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__8(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = l_Lean_IR_Decl_name___main(x_3);
x_9 = l_HashMapImp_insert___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__2(x_1, x_8, x_3);
x_1 = x_9;
x_2 = x_5;
goto _start;
}
}
}
obj* l_AssocList_foldl___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__9(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; 
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::array_push(x_0, x_2);
x_0 = x_7;
x_1 = x_4;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = l_AssocList_foldl___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__9(x_3, x_8);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_2, x_10);
lean::dec(x_2);
x_2 = x_11;
x_3 = x_9;
goto _start;
}
}
}
obj* _init_l___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(8ul);
x_1 = l_mkHashMapImp___rarg(x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_compilerm_4__mkEntryArray(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
x_1 = l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__2;
x_2 = l___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___closed__1;
x_3 = l_List_foldl___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__8(x_1, x_2, x_0);
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
x_6 = lean::mk_nat_obj(0ul);
x_7 = l_Array_empty___closed__1;
x_8 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__10(x_3, x_4, x_6, x_7);
lean::dec(x_4);
lean::dec(x_3);
return x_8;
}
}
obj* l_AssocList_contains___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_AssocList_contains___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__3(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_List_foldl___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__8___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_foldl___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__8(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__10___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__10(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_SMap_empty___at_Lean_IR_mkDeclMapExtension___spec__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; uint8 x_3; obj* x_4; obj* x_5; 
x_0 = lean::mk_nat_obj(8ul);
x_1 = l_mkHashMapImp___rarg(x_0);
x_2 = lean::box(0);
x_3 = 1;
x_4 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_3);
x_5 = x_4;
return x_5;
}
}
obj* l_Lean_SMap_switch___at_Lean_IR_mkDeclMapExtension___spec__2(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
if (x_1 == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_6 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = 0;
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 1);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_4);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_7);
x_9 = x_8;
return x_9;
}
}
}
obj* l_RBNode_ins___main___at_Lean_IR_mkDeclMapExtension___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = 0;
x_4 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_3);
x_5 = x_4;
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_11 = lean::cnstr_get(x_0, 2);
x_13 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_15 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_0);
 x_15 = lean::box(0);
}
x_16 = l_Lean_Name_quickLt(x_1, x_9);
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_Lean_Name_quickLt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_RBNode_ins___main___at_Lean_IR_mkDeclMapExtension___spec__5(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_RBNode_ins___main___at_Lean_IR_mkDeclMapExtension___spec__5(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
x_28 = lean::cnstr_get(x_0, 0);
x_30 = lean::cnstr_get(x_0, 1);
x_32 = lean::cnstr_get(x_0, 2);
x_34 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_36 = x_0;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_0);
 x_36 = lean::box(0);
}
x_37 = l_Lean_Name_quickLt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_Lean_Name_quickLt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_RBNode_isRed___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_RBNode_ins___main___at_Lean_IR_mkDeclMapExtension___spec__5(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; 
x_47 = l_RBNode_ins___main___at_Lean_IR_mkDeclMapExtension___spec__5(x_34, x_1, x_2);
if (lean::obj_tag(x_47) == 0)
{
lean::dec(x_32);
lean::dec(x_36);
lean::dec(x_30);
lean::dec(x_28);
return x_47;
}
else
{
obj* x_52; 
x_52 = lean::cnstr_get(x_47, 0);
lean::inc(x_52);
if (lean::obj_tag(x_52) == 0)
{
obj* x_54; 
x_54 = lean::cnstr_get(x_47, 3);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; obj* x_58; obj* x_60; uint8 x_61; obj* x_62; obj* x_63; uint8 x_64; obj* x_65; obj* x_66; 
x_56 = lean::cnstr_get(x_47, 1);
x_58 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_60 = x_47;
} else {
 lean::inc(x_56);
 lean::inc(x_58);
 lean::dec(x_47);
 x_60 = lean::box(0);
}
x_61 = 0;
if (lean::is_scalar(x_60)) {
 x_62 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_62 = x_60;
}
lean::cnstr_set(x_62, 0, x_54);
lean::cnstr_set(x_62, 1, x_56);
lean::cnstr_set(x_62, 2, x_58);
lean::cnstr_set(x_62, 3, x_54);
lean::cnstr_set_scalar(x_62, sizeof(void*)*4, x_61);
x_63 = x_62;
x_64 = 1;
if (lean::is_scalar(x_36)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_36;
}
lean::cnstr_set(x_65, 0, x_28);
lean::cnstr_set(x_65, 1, x_30);
lean::cnstr_set(x_65, 2, x_32);
lean::cnstr_set(x_65, 3, x_63);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_64);
x_66 = x_65;
return x_66;
}
else
{
uint8 x_67; 
x_67 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*4);
if (x_67 == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_75; obj* x_77; obj* x_79; obj* x_81; uint8 x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_68 = lean::cnstr_get(x_47, 1);
x_70 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_72 = x_47;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::dec(x_47);
 x_72 = lean::box(0);
}
x_73 = lean::cnstr_get(x_54, 0);
x_75 = lean::cnstr_get(x_54, 1);
x_77 = lean::cnstr_get(x_54, 2);
x_79 = lean::cnstr_get(x_54, 3);
if (lean::is_exclusive(x_54)) {
 x_81 = x_54;
} else {
 lean::inc(x_73);
 lean::inc(x_75);
 lean::inc(x_77);
 lean::inc(x_79);
 lean::dec(x_54);
 x_81 = lean::box(0);
}
x_82 = 1;
if (lean::is_scalar(x_81)) {
 x_83 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_83 = x_81;
}
lean::cnstr_set(x_83, 0, x_28);
lean::cnstr_set(x_83, 1, x_30);
lean::cnstr_set(x_83, 2, x_32);
lean::cnstr_set(x_83, 3, x_52);
lean::cnstr_set_scalar(x_83, sizeof(void*)*4, x_82);
x_84 = x_83;
if (lean::is_scalar(x_72)) {
 x_85 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_85 = x_72;
}
lean::cnstr_set(x_85, 0, x_73);
lean::cnstr_set(x_85, 1, x_75);
lean::cnstr_set(x_85, 2, x_77);
lean::cnstr_set(x_85, 3, x_79);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4, x_82);
x_86 = x_85;
if (lean::is_scalar(x_36)) {
 x_87 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_87 = x_36;
}
lean::cnstr_set(x_87, 0, x_84);
lean::cnstr_set(x_87, 1, x_68);
lean::cnstr_set(x_87, 2, x_70);
lean::cnstr_set(x_87, 3, x_86);
lean::cnstr_set_scalar(x_87, sizeof(void*)*4, x_67);
x_88 = x_87;
return x_88;
}
else
{
obj* x_89; obj* x_91; obj* x_93; uint8 x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_89 = lean::cnstr_get(x_47, 1);
x_91 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_93 = x_47;
} else {
 lean::inc(x_89);
 lean::inc(x_91);
 lean::dec(x_47);
 x_93 = lean::box(0);
}
x_94 = 0;
if (lean::is_scalar(x_93)) {
 x_95 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_95 = x_93;
}
lean::cnstr_set(x_95, 0, x_52);
lean::cnstr_set(x_95, 1, x_89);
lean::cnstr_set(x_95, 2, x_91);
lean::cnstr_set(x_95, 3, x_54);
lean::cnstr_set_scalar(x_95, sizeof(void*)*4, x_94);
x_96 = x_95;
if (lean::is_scalar(x_36)) {
 x_97 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_97 = x_36;
}
lean::cnstr_set(x_97, 0, x_28);
lean::cnstr_set(x_97, 1, x_30);
lean::cnstr_set(x_97, 2, x_32);
lean::cnstr_set(x_97, 3, x_96);
lean::cnstr_set_scalar(x_97, sizeof(void*)*4, x_67);
x_98 = x_97;
return x_98;
}
}
}
else
{
uint8 x_99; 
x_99 = lean::cnstr_get_scalar<uint8>(x_52, sizeof(void*)*4);
if (x_99 == 0)
{
obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_109; obj* x_111; obj* x_113; obj* x_115; uint8 x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
x_100 = lean::cnstr_get(x_47, 1);
x_102 = lean::cnstr_get(x_47, 2);
x_104 = lean::cnstr_get(x_47, 3);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 x_106 = x_47;
} else {
 lean::inc(x_100);
 lean::inc(x_102);
 lean::inc(x_104);
 lean::dec(x_47);
 x_106 = lean::box(0);
}
x_107 = lean::cnstr_get(x_52, 0);
x_109 = lean::cnstr_get(x_52, 1);
x_111 = lean::cnstr_get(x_52, 2);
x_113 = lean::cnstr_get(x_52, 3);
if (lean::is_exclusive(x_52)) {
 x_115 = x_52;
} else {
 lean::inc(x_107);
 lean::inc(x_109);
 lean::inc(x_111);
 lean::inc(x_113);
 lean::dec(x_52);
 x_115 = lean::box(0);
}
x_116 = 1;
if (lean::is_scalar(x_115)) {
 x_117 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_117 = x_115;
}
lean::cnstr_set(x_117, 0, x_28);
lean::cnstr_set(x_117, 1, x_30);
lean::cnstr_set(x_117, 2, x_32);
lean::cnstr_set(x_117, 3, x_107);
lean::cnstr_set_scalar(x_117, sizeof(void*)*4, x_116);
x_118 = x_117;
if (lean::is_scalar(x_106)) {
 x_119 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_119 = x_106;
}
lean::cnstr_set(x_119, 0, x_113);
lean::cnstr_set(x_119, 1, x_100);
lean::cnstr_set(x_119, 2, x_102);
lean::cnstr_set(x_119, 3, x_104);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_116);
x_120 = x_119;
if (lean::is_scalar(x_36)) {
 x_121 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_121 = x_36;
}
lean::cnstr_set(x_121, 0, x_118);
lean::cnstr_set(x_121, 1, x_109);
lean::cnstr_set(x_121, 2, x_111);
lean::cnstr_set(x_121, 3, x_120);
lean::cnstr_set_scalar(x_121, sizeof(void*)*4, x_99);
x_122 = x_121;
return x_122;
}
else
{
obj* x_123; 
x_123 = lean::cnstr_get(x_47, 3);
lean::inc(x_123);
if (lean::obj_tag(x_123) == 0)
{
obj* x_125; obj* x_127; obj* x_129; uint8 x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
x_125 = lean::cnstr_get(x_47, 1);
x_127 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_129 = x_47;
} else {
 lean::inc(x_125);
 lean::inc(x_127);
 lean::dec(x_47);
 x_129 = lean::box(0);
}
x_130 = 0;
if (lean::is_scalar(x_129)) {
 x_131 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_131 = x_129;
}
lean::cnstr_set(x_131, 0, x_52);
lean::cnstr_set(x_131, 1, x_125);
lean::cnstr_set(x_131, 2, x_127);
lean::cnstr_set(x_131, 3, x_123);
lean::cnstr_set_scalar(x_131, sizeof(void*)*4, x_130);
x_132 = x_131;
if (lean::is_scalar(x_36)) {
 x_133 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_133 = x_36;
}
lean::cnstr_set(x_133, 0, x_28);
lean::cnstr_set(x_133, 1, x_30);
lean::cnstr_set(x_133, 2, x_32);
lean::cnstr_set(x_133, 3, x_132);
lean::cnstr_set_scalar(x_133, sizeof(void*)*4, x_99);
x_134 = x_133;
return x_134;
}
else
{
uint8 x_135; 
x_135 = lean::cnstr_get_scalar<uint8>(x_123, sizeof(void*)*4);
if (x_135 == 0)
{
obj* x_137; obj* x_139; obj* x_141; obj* x_142; obj* x_144; obj* x_146; obj* x_148; obj* x_150; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
lean::dec(x_36);
x_137 = lean::cnstr_get(x_47, 1);
x_139 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_141 = x_47;
} else {
 lean::inc(x_137);
 lean::inc(x_139);
 lean::dec(x_47);
 x_141 = lean::box(0);
}
x_142 = lean::cnstr_get(x_123, 0);
x_144 = lean::cnstr_get(x_123, 1);
x_146 = lean::cnstr_get(x_123, 2);
x_148 = lean::cnstr_get(x_123, 3);
if (lean::is_exclusive(x_123)) {
 x_150 = x_123;
} else {
 lean::inc(x_142);
 lean::inc(x_144);
 lean::inc(x_146);
 lean::inc(x_148);
 lean::dec(x_123);
 x_150 = lean::box(0);
}
lean::inc(x_52);
if (lean::is_scalar(x_150)) {
 x_152 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_152 = x_150;
}
lean::cnstr_set(x_152, 0, x_28);
lean::cnstr_set(x_152, 1, x_30);
lean::cnstr_set(x_152, 2, x_32);
lean::cnstr_set(x_152, 3, x_52);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 lean::cnstr_release(x_52, 1);
 lean::cnstr_release(x_52, 2);
 lean::cnstr_release(x_52, 3);
 x_153 = x_52;
} else {
 lean::dec(x_52);
 x_153 = lean::box(0);
}
lean::cnstr_set_scalar(x_152, sizeof(void*)*4, x_99);
x_154 = x_152;
if (lean::is_scalar(x_153)) {
 x_155 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_155 = x_153;
}
lean::cnstr_set(x_155, 0, x_142);
lean::cnstr_set(x_155, 1, x_144);
lean::cnstr_set(x_155, 2, x_146);
lean::cnstr_set(x_155, 3, x_148);
lean::cnstr_set_scalar(x_155, sizeof(void*)*4, x_99);
x_156 = x_155;
if (lean::is_scalar(x_141)) {
 x_157 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_157 = x_141;
}
lean::cnstr_set(x_157, 0, x_154);
lean::cnstr_set(x_157, 1, x_137);
lean::cnstr_set(x_157, 2, x_139);
lean::cnstr_set(x_157, 3, x_156);
lean::cnstr_set_scalar(x_157, sizeof(void*)*4, x_135);
x_158 = x_157;
return x_158;
}
else
{
obj* x_159; obj* x_161; obj* x_163; obj* x_164; obj* x_166; obj* x_168; obj* x_170; obj* x_172; obj* x_173; obj* x_174; uint8 x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
x_159 = lean::cnstr_get(x_47, 1);
x_161 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_163 = x_47;
} else {
 lean::inc(x_159);
 lean::inc(x_161);
 lean::dec(x_47);
 x_163 = lean::box(0);
}
x_164 = lean::cnstr_get(x_52, 0);
x_166 = lean::cnstr_get(x_52, 1);
x_168 = lean::cnstr_get(x_52, 2);
x_170 = lean::cnstr_get(x_52, 3);
if (lean::is_exclusive(x_52)) {
 x_172 = x_52;
} else {
 lean::inc(x_164);
 lean::inc(x_166);
 lean::inc(x_168);
 lean::inc(x_170);
 lean::dec(x_52);
 x_172 = lean::box(0);
}
if (lean::is_scalar(x_172)) {
 x_173 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_173 = x_172;
}
lean::cnstr_set(x_173, 0, x_164);
lean::cnstr_set(x_173, 1, x_166);
lean::cnstr_set(x_173, 2, x_168);
lean::cnstr_set(x_173, 3, x_170);
lean::cnstr_set_scalar(x_173, sizeof(void*)*4, x_135);
x_174 = x_173;
x_175 = 0;
if (lean::is_scalar(x_163)) {
 x_176 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_176 = x_163;
}
lean::cnstr_set(x_176, 0, x_174);
lean::cnstr_set(x_176, 1, x_159);
lean::cnstr_set(x_176, 2, x_161);
lean::cnstr_set(x_176, 3, x_123);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_175);
x_177 = x_176;
if (lean::is_scalar(x_36)) {
 x_178 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_178 = x_36;
}
lean::cnstr_set(x_178, 0, x_28);
lean::cnstr_set(x_178, 1, x_30);
lean::cnstr_set(x_178, 2, x_32);
lean::cnstr_set(x_178, 3, x_177);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_135);
x_179 = x_178;
return x_179;
}
}
}
}
}
}
}
}
else
{
uint8 x_180; 
x_180 = l_RBNode_isRed___main___rarg(x_28);
if (x_180 == 0)
{
obj* x_181; obj* x_182; obj* x_183; 
x_181 = l_RBNode_ins___main___at_Lean_IR_mkDeclMapExtension___spec__5(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_182 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_182 = x_36;
}
lean::cnstr_set(x_182, 0, x_181);
lean::cnstr_set(x_182, 1, x_30);
lean::cnstr_set(x_182, 2, x_32);
lean::cnstr_set(x_182, 3, x_34);
lean::cnstr_set_scalar(x_182, sizeof(void*)*4, x_6);
x_183 = x_182;
return x_183;
}
else
{
obj* x_184; 
x_184 = l_RBNode_ins___main___at_Lean_IR_mkDeclMapExtension___spec__5(x_28, x_1, x_2);
if (lean::obj_tag(x_184) == 0)
{
lean::dec(x_32);
lean::dec(x_36);
lean::dec(x_30);
lean::dec(x_34);
return x_184;
}
else
{
obj* x_189; 
x_189 = lean::cnstr_get(x_184, 0);
lean::inc(x_189);
if (lean::obj_tag(x_189) == 0)
{
obj* x_191; 
x_191 = lean::cnstr_get(x_184, 3);
lean::inc(x_191);
if (lean::obj_tag(x_191) == 0)
{
obj* x_193; obj* x_195; obj* x_197; uint8 x_198; obj* x_199; obj* x_200; uint8 x_201; obj* x_202; obj* x_203; 
x_193 = lean::cnstr_get(x_184, 1);
x_195 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_197 = x_184;
} else {
 lean::inc(x_193);
 lean::inc(x_195);
 lean::dec(x_184);
 x_197 = lean::box(0);
}
x_198 = 0;
if (lean::is_scalar(x_197)) {
 x_199 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_199 = x_197;
}
lean::cnstr_set(x_199, 0, x_191);
lean::cnstr_set(x_199, 1, x_193);
lean::cnstr_set(x_199, 2, x_195);
lean::cnstr_set(x_199, 3, x_191);
lean::cnstr_set_scalar(x_199, sizeof(void*)*4, x_198);
x_200 = x_199;
x_201 = 1;
if (lean::is_scalar(x_36)) {
 x_202 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_202 = x_36;
}
lean::cnstr_set(x_202, 0, x_200);
lean::cnstr_set(x_202, 1, x_30);
lean::cnstr_set(x_202, 2, x_32);
lean::cnstr_set(x_202, 3, x_34);
lean::cnstr_set_scalar(x_202, sizeof(void*)*4, x_201);
x_203 = x_202;
return x_203;
}
else
{
uint8 x_204; 
x_204 = lean::cnstr_get_scalar<uint8>(x_191, sizeof(void*)*4);
if (x_204 == 0)
{
obj* x_205; obj* x_207; obj* x_209; obj* x_210; obj* x_212; obj* x_214; obj* x_216; obj* x_218; uint8 x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; 
x_205 = lean::cnstr_get(x_184, 1);
x_207 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_209 = x_184;
} else {
 lean::inc(x_205);
 lean::inc(x_207);
 lean::dec(x_184);
 x_209 = lean::box(0);
}
x_210 = lean::cnstr_get(x_191, 0);
x_212 = lean::cnstr_get(x_191, 1);
x_214 = lean::cnstr_get(x_191, 2);
x_216 = lean::cnstr_get(x_191, 3);
if (lean::is_exclusive(x_191)) {
 x_218 = x_191;
} else {
 lean::inc(x_210);
 lean::inc(x_212);
 lean::inc(x_214);
 lean::inc(x_216);
 lean::dec(x_191);
 x_218 = lean::box(0);
}
x_219 = 1;
if (lean::is_scalar(x_218)) {
 x_220 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_220 = x_218;
}
lean::cnstr_set(x_220, 0, x_189);
lean::cnstr_set(x_220, 1, x_205);
lean::cnstr_set(x_220, 2, x_207);
lean::cnstr_set(x_220, 3, x_210);
lean::cnstr_set_scalar(x_220, sizeof(void*)*4, x_219);
x_221 = x_220;
if (lean::is_scalar(x_209)) {
 x_222 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_222 = x_209;
}
lean::cnstr_set(x_222, 0, x_216);
lean::cnstr_set(x_222, 1, x_30);
lean::cnstr_set(x_222, 2, x_32);
lean::cnstr_set(x_222, 3, x_34);
lean::cnstr_set_scalar(x_222, sizeof(void*)*4, x_219);
x_223 = x_222;
if (lean::is_scalar(x_36)) {
 x_224 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_224 = x_36;
}
lean::cnstr_set(x_224, 0, x_221);
lean::cnstr_set(x_224, 1, x_212);
lean::cnstr_set(x_224, 2, x_214);
lean::cnstr_set(x_224, 3, x_223);
lean::cnstr_set_scalar(x_224, sizeof(void*)*4, x_204);
x_225 = x_224;
return x_225;
}
else
{
obj* x_226; obj* x_228; obj* x_230; uint8 x_231; obj* x_232; obj* x_233; obj* x_234; obj* x_235; 
x_226 = lean::cnstr_get(x_184, 1);
x_228 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_230 = x_184;
} else {
 lean::inc(x_226);
 lean::inc(x_228);
 lean::dec(x_184);
 x_230 = lean::box(0);
}
x_231 = 0;
if (lean::is_scalar(x_230)) {
 x_232 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_232 = x_230;
}
lean::cnstr_set(x_232, 0, x_189);
lean::cnstr_set(x_232, 1, x_226);
lean::cnstr_set(x_232, 2, x_228);
lean::cnstr_set(x_232, 3, x_191);
lean::cnstr_set_scalar(x_232, sizeof(void*)*4, x_231);
x_233 = x_232;
if (lean::is_scalar(x_36)) {
 x_234 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_234 = x_36;
}
lean::cnstr_set(x_234, 0, x_233);
lean::cnstr_set(x_234, 1, x_30);
lean::cnstr_set(x_234, 2, x_32);
lean::cnstr_set(x_234, 3, x_34);
lean::cnstr_set_scalar(x_234, sizeof(void*)*4, x_204);
x_235 = x_234;
return x_235;
}
}
}
else
{
uint8 x_236; 
x_236 = lean::cnstr_get_scalar<uint8>(x_189, sizeof(void*)*4);
if (x_236 == 0)
{
obj* x_237; obj* x_239; obj* x_241; obj* x_243; obj* x_244; obj* x_246; obj* x_248; obj* x_250; obj* x_252; uint8 x_253; obj* x_254; obj* x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; 
x_237 = lean::cnstr_get(x_184, 1);
x_239 = lean::cnstr_get(x_184, 2);
x_241 = lean::cnstr_get(x_184, 3);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 x_243 = x_184;
} else {
 lean::inc(x_237);
 lean::inc(x_239);
 lean::inc(x_241);
 lean::dec(x_184);
 x_243 = lean::box(0);
}
x_244 = lean::cnstr_get(x_189, 0);
x_246 = lean::cnstr_get(x_189, 1);
x_248 = lean::cnstr_get(x_189, 2);
x_250 = lean::cnstr_get(x_189, 3);
if (lean::is_exclusive(x_189)) {
 x_252 = x_189;
} else {
 lean::inc(x_244);
 lean::inc(x_246);
 lean::inc(x_248);
 lean::inc(x_250);
 lean::dec(x_189);
 x_252 = lean::box(0);
}
x_253 = 1;
if (lean::is_scalar(x_252)) {
 x_254 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_254 = x_252;
}
lean::cnstr_set(x_254, 0, x_244);
lean::cnstr_set(x_254, 1, x_246);
lean::cnstr_set(x_254, 2, x_248);
lean::cnstr_set(x_254, 3, x_250);
lean::cnstr_set_scalar(x_254, sizeof(void*)*4, x_253);
x_255 = x_254;
if (lean::is_scalar(x_243)) {
 x_256 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_256 = x_243;
}
lean::cnstr_set(x_256, 0, x_241);
lean::cnstr_set(x_256, 1, x_30);
lean::cnstr_set(x_256, 2, x_32);
lean::cnstr_set(x_256, 3, x_34);
lean::cnstr_set_scalar(x_256, sizeof(void*)*4, x_253);
x_257 = x_256;
if (lean::is_scalar(x_36)) {
 x_258 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_258 = x_36;
}
lean::cnstr_set(x_258, 0, x_255);
lean::cnstr_set(x_258, 1, x_237);
lean::cnstr_set(x_258, 2, x_239);
lean::cnstr_set(x_258, 3, x_257);
lean::cnstr_set_scalar(x_258, sizeof(void*)*4, x_236);
x_259 = x_258;
return x_259;
}
else
{
obj* x_260; 
x_260 = lean::cnstr_get(x_184, 3);
lean::inc(x_260);
if (lean::obj_tag(x_260) == 0)
{
obj* x_262; obj* x_264; obj* x_266; uint8 x_267; obj* x_268; obj* x_269; obj* x_270; obj* x_271; 
x_262 = lean::cnstr_get(x_184, 1);
x_264 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_266 = x_184;
} else {
 lean::inc(x_262);
 lean::inc(x_264);
 lean::dec(x_184);
 x_266 = lean::box(0);
}
x_267 = 0;
if (lean::is_scalar(x_266)) {
 x_268 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_268 = x_266;
}
lean::cnstr_set(x_268, 0, x_189);
lean::cnstr_set(x_268, 1, x_262);
lean::cnstr_set(x_268, 2, x_264);
lean::cnstr_set(x_268, 3, x_260);
lean::cnstr_set_scalar(x_268, sizeof(void*)*4, x_267);
x_269 = x_268;
if (lean::is_scalar(x_36)) {
 x_270 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_270 = x_36;
}
lean::cnstr_set(x_270, 0, x_269);
lean::cnstr_set(x_270, 1, x_30);
lean::cnstr_set(x_270, 2, x_32);
lean::cnstr_set(x_270, 3, x_34);
lean::cnstr_set_scalar(x_270, sizeof(void*)*4, x_236);
x_271 = x_270;
return x_271;
}
else
{
uint8 x_272; 
x_272 = lean::cnstr_get_scalar<uint8>(x_260, sizeof(void*)*4);
if (x_272 == 0)
{
obj* x_274; obj* x_276; obj* x_278; obj* x_279; obj* x_281; obj* x_283; obj* x_285; obj* x_287; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; 
lean::dec(x_36);
x_274 = lean::cnstr_get(x_184, 1);
x_276 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_278 = x_184;
} else {
 lean::inc(x_274);
 lean::inc(x_276);
 lean::dec(x_184);
 x_278 = lean::box(0);
}
x_279 = lean::cnstr_get(x_260, 0);
x_281 = lean::cnstr_get(x_260, 1);
x_283 = lean::cnstr_get(x_260, 2);
x_285 = lean::cnstr_get(x_260, 3);
if (lean::is_exclusive(x_260)) {
 x_287 = x_260;
} else {
 lean::inc(x_279);
 lean::inc(x_281);
 lean::inc(x_283);
 lean::inc(x_285);
 lean::dec(x_260);
 x_287 = lean::box(0);
}
lean::inc(x_189);
if (lean::is_scalar(x_287)) {
 x_289 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_289 = x_287;
}
lean::cnstr_set(x_289, 0, x_189);
lean::cnstr_set(x_289, 1, x_274);
lean::cnstr_set(x_289, 2, x_276);
lean::cnstr_set(x_289, 3, x_279);
if (lean::is_exclusive(x_189)) {
 lean::cnstr_release(x_189, 0);
 lean::cnstr_release(x_189, 1);
 lean::cnstr_release(x_189, 2);
 lean::cnstr_release(x_189, 3);
 x_290 = x_189;
} else {
 lean::dec(x_189);
 x_290 = lean::box(0);
}
lean::cnstr_set_scalar(x_289, sizeof(void*)*4, x_236);
x_291 = x_289;
if (lean::is_scalar(x_290)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_290;
}
lean::cnstr_set(x_292, 0, x_285);
lean::cnstr_set(x_292, 1, x_30);
lean::cnstr_set(x_292, 2, x_32);
lean::cnstr_set(x_292, 3, x_34);
lean::cnstr_set_scalar(x_292, sizeof(void*)*4, x_236);
x_293 = x_292;
if (lean::is_scalar(x_278)) {
 x_294 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_294 = x_278;
}
lean::cnstr_set(x_294, 0, x_291);
lean::cnstr_set(x_294, 1, x_281);
lean::cnstr_set(x_294, 2, x_283);
lean::cnstr_set(x_294, 3, x_293);
lean::cnstr_set_scalar(x_294, sizeof(void*)*4, x_272);
x_295 = x_294;
return x_295;
}
else
{
obj* x_296; obj* x_298; obj* x_300; obj* x_301; obj* x_303; obj* x_305; obj* x_307; obj* x_309; obj* x_310; obj* x_311; uint8 x_312; obj* x_313; obj* x_314; obj* x_315; obj* x_316; 
x_296 = lean::cnstr_get(x_184, 1);
x_298 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_300 = x_184;
} else {
 lean::inc(x_296);
 lean::inc(x_298);
 lean::dec(x_184);
 x_300 = lean::box(0);
}
x_301 = lean::cnstr_get(x_189, 0);
x_303 = lean::cnstr_get(x_189, 1);
x_305 = lean::cnstr_get(x_189, 2);
x_307 = lean::cnstr_get(x_189, 3);
if (lean::is_exclusive(x_189)) {
 x_309 = x_189;
} else {
 lean::inc(x_301);
 lean::inc(x_303);
 lean::inc(x_305);
 lean::inc(x_307);
 lean::dec(x_189);
 x_309 = lean::box(0);
}
if (lean::is_scalar(x_309)) {
 x_310 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_310 = x_309;
}
lean::cnstr_set(x_310, 0, x_301);
lean::cnstr_set(x_310, 1, x_303);
lean::cnstr_set(x_310, 2, x_305);
lean::cnstr_set(x_310, 3, x_307);
lean::cnstr_set_scalar(x_310, sizeof(void*)*4, x_272);
x_311 = x_310;
x_312 = 0;
if (lean::is_scalar(x_300)) {
 x_313 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_313 = x_300;
}
lean::cnstr_set(x_313, 0, x_311);
lean::cnstr_set(x_313, 1, x_296);
lean::cnstr_set(x_313, 2, x_298);
lean::cnstr_set(x_313, 3, x_260);
lean::cnstr_set_scalar(x_313, sizeof(void*)*4, x_312);
x_314 = x_313;
if (lean::is_scalar(x_36)) {
 x_315 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_315 = x_36;
}
lean::cnstr_set(x_315, 0, x_314);
lean::cnstr_set(x_315, 1, x_30);
lean::cnstr_set(x_315, 2, x_32);
lean::cnstr_set(x_315, 3, x_34);
lean::cnstr_set_scalar(x_315, sizeof(void*)*4, x_272);
x_316 = x_315;
return x_316;
}
}
}
}
}
}
}
}
}
}
}
obj* l_RBNode_insert___at_Lean_IR_mkDeclMapExtension___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_RBNode_isRed___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at_Lean_IR_mkDeclMapExtension___spec__5(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_RBNode_ins___main___at_Lean_IR_mkDeclMapExtension___spec__5(x_0, x_1, x_2);
x_6 = l_RBNode_setBlack___main___rarg(x_5);
return x_6;
}
}
}
obj* l_Lean_SMap_insert___main___at_Lean_IR_mkDeclMapExtension___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
if (x_3 == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_0, 0);
x_6 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_8 = x_0;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
x_9 = l_RBNode_insert___at_Lean_IR_mkDeclMapExtension___spec__4(x_6, x_1, x_2);
if (lean::is_scalar(x_8)) {
 x_10 = lean::alloc_cnstr(0, 2, 1);
} else {
 x_10 = x_8;
}
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_9);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_3);
x_11 = x_10;
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_12 = lean::cnstr_get(x_0, 0);
x_14 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_16 = x_0;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_0);
 x_16 = lean::box(0);
}
x_17 = l_HashMapImp_insert___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__2(x_12, x_1, x_2);
if (lean::is_scalar(x_16)) {
 x_18 = lean::alloc_cnstr(0, 2, 1);
} else {
 x_18 = x_16;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_14);
lean::cnstr_set_scalar(x_18, sizeof(void*)*2, x_3);
x_19 = x_18;
return x_19;
}
}
}
uint8 l_Array_anyMAux___main___at_Lean_IR_mkDeclMapExtension___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_7; 
lean::dec(x_2);
x_7 = 0;
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_12; uint8 x_13; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::cnstr_get(x_0, 0);
x_13 = lean_name_dec_eq(x_9, x_12);
lean::dec(x_9);
if (x_13 == 0)
{
obj* x_15; obj* x_16; 
x_15 = lean::mk_nat_obj(1ul);
x_16 = lean::nat_add(x_2, x_15);
lean::dec(x_2);
x_2 = x_16;
goto _start;
}
else
{
lean::dec(x_2);
return x_13;
}
}
}
}
obj* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_mkDeclMapExtension___spec__6(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; uint8 x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 3);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 4);
lean::inc(x_10);
x_12 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*5);
lean::inc(x_4);
x_14 = lean::thunk_pure(x_4);
x_15 = lean::box(0);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_4);
x_17 = l_Array_empty___closed__1;
x_18 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_14);
lean::cnstr_set(x_18, 2, x_15);
lean::cnstr_set(x_18, 3, x_16);
x_19 = l___private_init_lean_environment_9__persistentEnvExtensionsRef;
x_20 = lean::io_ref_get(x_19, x_1);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_23; obj* x_25; obj* x_26; uint8 x_27; 
x_21 = lean::cnstr_get(x_20, 0);
x_23 = lean::cnstr_get(x_20, 1);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_set(x_20, 0, lean::box(0));
 lean::cnstr_set(x_20, 1, lean::box(0));
 x_25 = x_20;
} else {
 lean::inc(x_21);
 lean::inc(x_23);
 lean::dec(x_20);
 x_25 = lean::box(0);
}
x_26 = lean::mk_nat_obj(0ul);
x_27 = l_Array_anyMAux___main___at_Lean_IR_mkDeclMapExtension___spec__7(x_0, x_21, x_26);
lean::dec(x_21);
lean::dec(x_0);
if (x_27 == 0)
{
obj* x_30; obj* x_31; obj* x_32; 
x_30 = lean::box(0);
if (lean::is_scalar(x_25)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_25;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_23);
x_32 = l_Lean_registerEnvExtensionUnsafe___rarg(x_18, x_31);
if (lean::obj_tag(x_32) == 0)
{
obj* x_33; obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_33 = lean::cnstr_get(x_32, 0);
x_35 = lean::cnstr_get(x_32, 1);
if (lean::is_exclusive(x_32)) {
 x_37 = x_32;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_32);
 x_37 = lean::box(0);
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_30);
lean::cnstr_set(x_38, 1, x_35);
x_39 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_39, 0, x_33);
lean::cnstr_set(x_39, 1, x_2);
lean::cnstr_set(x_39, 2, x_6);
lean::cnstr_set(x_39, 3, x_8);
lean::cnstr_set(x_39, 4, x_10);
lean::cnstr_set_scalar(x_39, sizeof(void*)*5, x_12);
x_40 = x_39;
x_41 = lean::io_ref_get(x_19, x_38);
if (lean::obj_tag(x_41) == 0)
{
obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_48; 
x_42 = lean::cnstr_get(x_41, 0);
x_44 = lean::cnstr_get(x_41, 1);
if (lean::is_exclusive(x_41)) {
 x_46 = x_41;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::dec(x_41);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_30);
lean::cnstr_set(x_47, 1, x_44);
x_48 = lean::io_ref_reset(x_19, x_47);
if (lean::obj_tag(x_48) == 0)
{
obj* x_49; obj* x_51; obj* x_52; obj* x_53; obj* x_55; obj* x_56; obj* x_57; 
x_49 = lean::cnstr_get(x_48, 1);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 x_51 = x_48;
} else {
 lean::inc(x_49);
 lean::dec(x_48);
 x_51 = lean::box(0);
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_30);
lean::cnstr_set(x_52, 1, x_49);
x_53 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean::inc(x_40);
x_55 = x_40;
x_56 = lean::array_push(x_42, x_55);
x_57 = lean::io_ref_set(x_19, x_56, x_52);
if (lean::obj_tag(x_57) == 0)
{
obj* x_58; obj* x_60; obj* x_61; 
x_58 = lean::cnstr_get(x_57, 1);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 x_60 = x_57;
} else {
 lean::inc(x_58);
 lean::dec(x_57);
 x_60 = lean::box(0);
}
if (lean::is_scalar(x_60)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_60;
}
lean::cnstr_set(x_61, 0, x_40);
lean::cnstr_set(x_61, 1, x_58);
return x_61;
}
else
{
obj* x_63; obj* x_65; obj* x_67; obj* x_68; 
lean::dec(x_40);
x_63 = lean::cnstr_get(x_57, 0);
x_65 = lean::cnstr_get(x_57, 1);
if (lean::is_exclusive(x_57)) {
 x_67 = x_57;
} else {
 lean::inc(x_63);
 lean::inc(x_65);
 lean::dec(x_57);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_63);
lean::cnstr_set(x_68, 1, x_65);
return x_68;
}
}
else
{
obj* x_71; obj* x_73; obj* x_75; obj* x_76; 
lean::dec(x_40);
lean::dec(x_42);
x_71 = lean::cnstr_get(x_48, 0);
x_73 = lean::cnstr_get(x_48, 1);
if (lean::is_exclusive(x_48)) {
 x_75 = x_48;
} else {
 lean::inc(x_71);
 lean::inc(x_73);
 lean::dec(x_48);
 x_75 = lean::box(0);
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_71);
lean::cnstr_set(x_76, 1, x_73);
return x_76;
}
}
else
{
obj* x_78; obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_40);
x_78 = lean::cnstr_get(x_41, 0);
x_80 = lean::cnstr_get(x_41, 1);
if (lean::is_exclusive(x_41)) {
 x_82 = x_41;
} else {
 lean::inc(x_78);
 lean::inc(x_80);
 lean::dec(x_41);
 x_82 = lean::box(0);
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_83 = x_82;
}
lean::cnstr_set(x_83, 0, x_78);
lean::cnstr_set(x_83, 1, x_80);
return x_83;
}
}
else
{
obj* x_88; obj* x_90; obj* x_92; obj* x_93; 
lean::dec(x_8);
lean::dec(x_6);
lean::dec(x_10);
lean::dec(x_2);
x_88 = lean::cnstr_get(x_32, 0);
x_90 = lean::cnstr_get(x_32, 1);
if (lean::is_exclusive(x_32)) {
 x_92 = x_32;
} else {
 lean::inc(x_88);
 lean::inc(x_90);
 lean::dec(x_32);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_88);
lean::cnstr_set(x_93, 1, x_90);
return x_93;
}
}
else
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_103; obj* x_104; obj* x_105; 
lean::dec(x_8);
lean::dec(x_6);
lean::dec(x_10);
lean::dec(x_18);
x_98 = l_Lean_Name_toString___closed__1;
x_99 = l_Lean_Name_toStringWithSep___main(x_98, x_2);
x_100 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_101 = lean::string_append(x_100, x_99);
lean::dec(x_99);
x_103 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_104 = lean::string_append(x_101, x_103);
if (lean::is_scalar(x_25)) {
 x_105 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_105 = x_25;
 lean::cnstr_set_tag(x_25, 1);
}
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_23);
return x_105;
}
}
else
{
obj* x_112; obj* x_114; obj* x_116; obj* x_117; 
lean::dec(x_8);
lean::dec(x_6);
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_18);
lean::dec(x_2);
x_112 = lean::cnstr_get(x_20, 0);
x_114 = lean::cnstr_get(x_20, 1);
if (lean::is_exclusive(x_20)) {
 x_116 = x_20;
} else {
 lean::inc(x_112);
 lean::inc(x_114);
 lean::dec(x_20);
 x_116 = lean::box(0);
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_112);
lean::cnstr_set(x_117, 1, x_114);
return x_117;
}
}
}
obj* l_Lean_IR_mkDeclMapExtension___lambda__1(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Decl_name___main(x_2);
if (x_0 == 0)
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_SMap_switch___at_Lean_IR_mkDeclMapExtension___spec__2(x_1);
x_5 = l_Lean_SMap_insert___main___at_Lean_IR_mkDeclMapExtension___spec__3(x_4, x_3, x_2);
return x_5;
}
else
{
obj* x_6; 
x_6 = l_Lean_SMap_insert___main___at_Lean_IR_mkDeclMapExtension___spec__3(x_1, x_3, x_2);
return x_6;
}
}
}
obj* _init_l_Lean_IR_mkDeclMapExtension___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; uint8 x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_14; 
x_0 = lean::box(0);
x_1 = lean::mk_string("IRDecls");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_nat_obj(0ul);
x_4 = lean::mk_empty_array(x_3);
x_5 = 6;
x_6 = lean::box(12);
x_7 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_6);
lean::cnstr_set_scalar(x_7, sizeof(void*)*3, x_5);
x_8 = x_7;
x_9 = l_Lean_SMap_empty___at_Lean_IR_mkDeclMapExtension___spec__1;
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_mkDeclMapExtension___lambda__1___boxed), 3, 0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_compilerm_4__mkEntryArray), 1, 0);
x_12 = 0;
x_13 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_13, 0, x_2);
lean::cnstr_set(x_13, 1, x_9);
lean::cnstr_set(x_13, 2, x_8);
lean::cnstr_set(x_13, 3, x_10);
lean::cnstr_set(x_13, 4, x_11);
lean::cnstr_set_scalar(x_13, sizeof(void*)*5, x_12);
x_14 = x_13;
return x_14;
}
}
obj* l_Lean_IR_mkDeclMapExtension(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_IR_mkDeclMapExtension___closed__1;
x_2 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_mkDeclMapExtension___spec__6(x_1, x_0);
return x_2;
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_mkDeclMapExtension___spec__7___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_anyMAux___main___at_Lean_IR_mkDeclMapExtension___spec__7(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_mkDeclMapExtension___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_Lean_IR_mkDeclMapExtension___lambda__1(x_3, x_1, x_2);
return x_4;
}
}
obj* l_Lean_IR_declMapExt___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_1 = l_List_redLength___main___rarg(x_0);
x_2 = lean::mk_empty_array(x_1);
lean::dec(x_1);
x_4 = l_List_toArrayAux___main___rarg(x_0, x_2);
return x_4;
}
}
obj* l_Lean_IR_declMapExt___elambda__2___rarg(obj* x_0, obj* x_1) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_Lean_IR_declMapExt___elambda__2(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_declMapExt___elambda__2___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Lean_IR_declMapExt___elambda__2___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_declMapExt___elambda__2___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_IR_declMapExt___elambda__2___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_Lean_IR_declMapExt___elambda__2(x_1);
return x_2;
}
}
obj* l_RBNode_find___main___at_Lean_IR_findEnvDecl___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; uint8 x_12; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_Lean_Name_quickLt(x_1, x_5);
if (x_12 == 0)
{
uint8 x_14; 
lean::dec(x_3);
x_14 = l_Lean_Name_quickLt(x_5, x_1);
lean::dec(x_5);
if (x_14 == 0)
{
obj* x_17; 
lean::dec(x_9);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_7);
return x_17;
}
else
{
lean::dec(x_7);
x_0 = x_9;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_5);
x_0 = x_3;
goto _start;
}
}
}
}
obj* l_AssocList_find___main___at_Lean_IR_findEnvDecl___spec__4(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; uint8 x_10; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 2);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean_name_dec_eq(x_3, x_0);
lean::dec(x_3);
if (x_10 == 0)
{
lean::dec(x_5);
x_1 = x_7;
goto _start;
}
else
{
obj* x_15; 
lean::dec(x_7);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_5);
return x_15;
}
}
}
}
obj* l_HashMapImp_find___at_Lean_IR_findEnvDecl___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; usize x_4; usize x_5; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 1);
x_3 = lean::array_get_size(x_2);
x_4 = lean_name_hash_usize(x_1);
x_5 = lean::usize_modn(x_4, x_3);
lean::dec(x_3);
x_7 = lean::array_uget(x_2, x_5);
x_8 = l_AssocList_find___main___at_Lean_IR_findEnvDecl___spec__4(x_1, x_7);
return x_8;
}
}
obj* l_Lean_SMap_find___main___at_Lean_IR_findEnvDecl___spec__1(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
if (x_2 == 0)
{
obj* x_3; obj* x_5; obj* x_8; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_RBNode_find___main___at_Lean_IR_findEnvDecl___spec__2(x_5, x_1);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; 
x_9 = l_HashMapImp_find___at_Lean_IR_findEnvDecl___spec__3(x_3, x_1);
lean::dec(x_3);
return x_9;
}
else
{
lean::dec(x_3);
return x_8;
}
}
else
{
obj* x_12; obj* x_15; 
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
lean::dec(x_0);
x_15 = l_HashMapImp_find___at_Lean_IR_findEnvDecl___spec__3(x_12, x_1);
lean::dec(x_12);
return x_15;
}
}
}
obj* l_Lean_IR_findEnvDecl(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_IR_declMapExt;
x_3 = l_Lean_PersistentEnvExtension_getState___rarg(x_2, x_0);
x_4 = l_Lean_SMap_find___main___at_Lean_IR_findEnvDecl___spec__1(x_3, x_1);
return x_4;
}
}
obj* l_RBNode_find___main___at_Lean_IR_findEnvDecl___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_Lean_IR_findEnvDecl___spec__2(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_AssocList_find___main___at_Lean_IR_findEnvDecl___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_AssocList_find___main___at_Lean_IR_findEnvDecl___spec__4(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_HashMapImp_find___at_Lean_IR_findEnvDecl___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashMapImp_find___at_Lean_IR_findEnvDecl___spec__3(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_SMap_find___main___at_Lean_IR_findEnvDecl___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SMap_find___main___at_Lean_IR_findEnvDecl___spec__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_IR_findEnvDecl___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_findEnvDecl(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_IR_findDecl(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = l_Lean_IR_findEnvDecl(x_6, x_0);
lean::dec(x_6);
if (lean::is_scalar(x_5)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_5;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l_Lean_IR_findDecl___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_findDecl(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_HashMapImp_contains___at_Lean_IR_containsDecl___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; usize x_4; usize x_5; obj* x_7; uint8 x_8; 
x_2 = lean::cnstr_get(x_0, 1);
x_3 = lean::array_get_size(x_2);
x_4 = lean_name_hash_usize(x_1);
x_5 = lean::usize_modn(x_4, x_3);
lean::dec(x_3);
x_7 = lean::array_uget(x_2, x_5);
x_8 = l_AssocList_contains___main___at___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___spec__3(x_1, x_7);
lean::dec(x_7);
return x_8;
}
}
uint8 l_Lean_SMap_contains___main___at_Lean_IR_containsDecl___spec__1(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
if (x_2 == 0)
{
obj* x_3; obj* x_5; uint8 x_8; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_HashMapImp_contains___at_Lean_IR_containsDecl___spec__2(x_3, x_1);
lean::dec(x_3);
if (x_8 == 0)
{
obj* x_10; 
x_10 = l_RBNode_find___main___at_Lean_IR_findEnvDecl___spec__2(x_5, x_1);
if (lean::obj_tag(x_10) == 0)
{
uint8 x_11; 
x_11 = 0;
return x_11;
}
else
{
uint8 x_13; 
lean::dec(x_10);
x_13 = 1;
return x_13;
}
}
else
{
uint8 x_15; 
lean::dec(x_5);
x_15 = 1;
return x_15;
}
}
else
{
obj* x_16; uint8 x_19; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
x_19 = l_HashMapImp_contains___at_Lean_IR_containsDecl___spec__2(x_16, x_1);
lean::dec(x_16);
return x_19;
}
}
}
obj* l_Lean_IR_containsDecl(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_9; uint8 x_11; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = l_Lean_IR_declMapExt;
x_9 = l_Lean_PersistentEnvExtension_getState___rarg(x_8, x_6);
lean::dec(x_6);
x_11 = l_Lean_SMap_contains___main___at_Lean_IR_containsDecl___spec__1(x_9, x_0);
x_12 = lean::box(x_11);
if (lean::is_scalar(x_5)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_5;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_3);
return x_13;
}
}
obj* l_HashMapImp_contains___at_Lean_IR_containsDecl___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_HashMapImp_contains___at_Lean_IR_containsDecl___spec__2(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_SMap_contains___main___at_Lean_IR_containsDecl___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_SMap_contains___main___at_Lean_IR_containsDecl___spec__1(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_containsDecl___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_containsDecl(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_IR_getDecl___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unknown declaration '");
return x_0;
}
}
obj* l_Lean_IR_getDecl(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_findDecl(x_0, x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; 
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_8 = x_3;
} else {
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = l_Lean_Name_toString___closed__1;
x_10 = l_Lean_Name_toStringWithSep___main(x_9, x_0);
x_11 = l_Lean_IR_getDecl___closed__1;
x_12 = lean::string_append(x_11, x_10);
lean::dec(x_10);
x_14 = l_Char_HasRepr___closed__1;
x_15 = lean::string_append(x_12, x_14);
if (lean::is_scalar(x_8)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_8;
 lean::cnstr_set_tag(x_8, 1);
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_6);
return x_16;
}
else
{
obj* x_18; obj* x_20; obj* x_21; obj* x_24; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_20 = x_3;
} else {
 lean::inc(x_18);
 lean::dec(x_3);
 x_20 = lean::box(0);
}
x_21 = lean::cnstr_get(x_4, 0);
lean::inc(x_21);
lean::dec(x_4);
if (lean::is_scalar(x_20)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_20;
}
lean::cnstr_set(x_24, 0, x_21);
lean::cnstr_set(x_24, 1, x_18);
return x_24;
}
}
else
{
obj* x_26; obj* x_28; obj* x_30; obj* x_31; 
lean::dec(x_0);
x_26 = lean::cnstr_get(x_3, 0);
x_28 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_30 = x_3;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_3);
 x_30 = lean::box(0);
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_26);
lean::cnstr_set(x_31, 1, x_28);
return x_31;
}
}
}
obj* l_Lean_IR_getDecl___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_getDecl(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
namespace lean {
namespace ir {
obj* add_decl_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_IR_declMapExt;
x_3 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_2, x_0, x_1);
return x_3;
}
}
}}
obj* l_Lean_IR_getDecls(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_IR_declMapExt;
x_2 = l_Lean_PersistentEnvExtension_getEntries___rarg(x_1, x_0);
return x_2;
}
}
obj* l_Lean_IR_getDecls___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_getDecls(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_getEnv___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_6; 
x_1 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_3 = x_0;
} else {
 lean::inc(x_1);
 lean::dec(x_0);
 x_3 = lean::box(0);
}
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
if (lean::is_scalar(x_3)) {
 x_6 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_6 = x_3;
}
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
obj* l_Lean_IR_getEnv(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_getEnv___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_IR_getEnv___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_getEnv(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_addDecl(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_10 = x_3;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
x_11 = l_Lean_IR_declMapExt;
x_12 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_11, x_6, x_0);
if (lean::is_scalar(x_10)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_10;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_8);
x_14 = lean::box(0);
if (lean::is_scalar(x_5)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_5;
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_13);
return x_15;
}
}
obj* l_Lean_IR_addDecl___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_addDecl(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_0);
x_5 = lean::nat_dec_lt(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_8 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_10 = x_3;
} else {
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
x_11 = lean::box(0);
if (lean::is_scalar(x_10)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_10;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_8);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_17; 
x_13 = lean::array_fget(x_0, x_1);
x_14 = lean::mk_nat_obj(1ul);
x_15 = lean::nat_add(x_1, x_14);
lean::dec(x_1);
x_17 = l_Lean_IR_addDecl(x_13, x_2, x_3);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
x_18 = lean::cnstr_get(x_17, 1);
if (lean::is_exclusive(x_17)) {
 lean::cnstr_release(x_17, 0);
 x_20 = x_17;
} else {
 lean::inc(x_18);
 lean::dec(x_17);
 x_20 = lean::box(0);
}
x_21 = lean::box(0);
if (lean::is_scalar(x_20)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_20;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_18);
x_1 = x_15;
x_3 = x_22;
goto _start;
}
else
{
obj* x_25; obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_15);
x_25 = lean::cnstr_get(x_17, 0);
x_27 = lean::cnstr_get(x_17, 1);
if (lean::is_exclusive(x_17)) {
 x_29 = x_17;
} else {
 lean::inc(x_25);
 lean::inc(x_27);
 lean::dec(x_17);
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
}
obj* l_Lean_IR_addDecls(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_0, x_3, x_1, x_2);
return x_4;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_IR_addDecls___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_addDecls(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_mfindAux___main___at_Lean_IR_findDeclAux_x_27___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_7; 
lean::dec(x_2);
x_7 = lean::box(0);
return x_7;
}
else
{
obj* x_8; obj* x_9; uint8 x_10; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = l_Lean_IR_Decl_name___main(x_8);
x_10 = lean_name_dec_eq(x_9, x_0);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_13; obj* x_14; 
lean::dec(x_8);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_2, x_13);
lean::dec(x_2);
x_2 = x_14;
goto _start;
}
else
{
obj* x_18; 
lean::dec(x_2);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_8);
return x_18;
}
}
}
}
obj* l_Lean_IR_findDeclAux_x_27(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_mfindAux___main___at_Lean_IR_findDeclAux_x_27___spec__1(x_1, x_2, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_IR_declMapExt;
x_6 = l_Lean_PersistentEnvExtension_getState___rarg(x_5, x_0);
x_7 = l_Lean_SMap_find___main___at_Lean_IR_findEnvDecl___spec__1(x_6, x_1);
return x_7;
}
else
{
return x_4;
}
}
}
obj* l_Array_mfindAux___main___at_Lean_IR_findDeclAux_x_27___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_mfindAux___main___at_Lean_IR_findDeclAux_x_27___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_findDeclAux_x_27___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_findDeclAux_x_27(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_IR_findDecl_x_27(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_4 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_6 = x_3;
} else {
 lean::inc(x_4);
 lean::dec(x_3);
 x_6 = lean::box(0);
}
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_9 = l_Lean_IR_findDeclAux_x_27(x_7, x_0, x_1);
lean::dec(x_7);
if (lean::is_scalar(x_6)) {
 x_11 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_11 = x_6;
}
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_4);
return x_11;
}
}
obj* l_Lean_IR_findDecl_x_27___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_findDecl_x_27(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
uint8 l_Array_anyMAux___main___at_Lean_IR_containsDecl_x_27___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_7; 
lean::dec(x_2);
x_7 = 0;
return x_7;
}
else
{
obj* x_8; obj* x_9; uint8 x_11; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = l_Lean_IR_Decl_name___main(x_8);
lean::dec(x_8);
x_11 = lean_name_dec_eq(x_9, x_0);
lean::dec(x_9);
if (x_11 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_2, x_13);
lean::dec(x_2);
x_2 = x_14;
goto _start;
}
else
{
lean::dec(x_2);
return x_11;
}
}
}
}
obj* l_Lean_IR_containsDecl_x_27(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_Array_anyMAux___main___at_Lean_IR_containsDecl_x_27___spec__1(x_0, x_1, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; uint8 x_14; obj* x_15; obj* x_16; 
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_8 = x_3;
} else {
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
x_11 = l_Lean_IR_declMapExt;
x_12 = l_Lean_PersistentEnvExtension_getState___rarg(x_11, x_9);
lean::dec(x_9);
x_14 = l_Lean_SMap_contains___main___at_Lean_IR_containsDecl___spec__1(x_12, x_0);
x_15 = lean::box(x_14);
if (lean::is_scalar(x_8)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_8;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_6);
return x_16;
}
else
{
obj* x_17; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; 
x_17 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_19 = x_3;
} else {
 lean::inc(x_17);
 lean::dec(x_3);
 x_19 = lean::box(0);
}
x_20 = 1;
x_21 = lean::box(x_20);
if (lean::is_scalar(x_19)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_19;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_17);
return x_22;
}
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_containsDecl_x_27___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_anyMAux___main___at_Lean_IR_containsDecl_x_27___spec__1(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_containsDecl_x_27___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_containsDecl_x_27(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_IR_getDecl_x_27(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_findDecl_x_27(x_0, x_1, x_2, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = l_Lean_Name_toString___closed__1;
x_11 = l_Lean_Name_toStringWithSep___main(x_10, x_0);
x_12 = l_Lean_IR_getDecl___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_15 = l_Char_HasRepr___closed__1;
x_16 = lean::string_append(x_13, x_15);
if (lean::is_scalar(x_9)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_9;
 lean::cnstr_set_tag(x_9, 1);
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_7);
return x_17;
}
else
{
obj* x_19; obj* x_21; obj* x_22; obj* x_25; 
lean::dec(x_0);
x_19 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_21 = x_4;
} else {
 lean::inc(x_19);
 lean::dec(x_4);
 x_21 = lean::box(0);
}
x_22 = lean::cnstr_get(x_5, 0);
lean::inc(x_22);
lean::dec(x_5);
if (lean::is_scalar(x_21)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_21;
}
lean::cnstr_set(x_25, 0, x_22);
lean::cnstr_set(x_25, 1, x_19);
return x_25;
}
}
else
{
obj* x_27; obj* x_29; obj* x_31; obj* x_32; 
lean::dec(x_0);
x_27 = lean::cnstr_get(x_4, 0);
x_29 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_31 = x_4;
} else {
 lean::inc(x_27);
 lean::inc(x_29);
 lean::dec(x_4);
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
obj* l_Lean_IR_getDecl_x_27___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_getDecl_x_27(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* initialize_init_control_reader(obj*);
obj* initialize_init_lean_environment(obj*);
obj* initialize_init_lean_compiler_ir_basic(obj*);
obj* initialize_init_lean_compiler_ir_format(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_compilerm(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_control_reader(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_environment(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_format(w);
if (io_result_is_error(w)) return w;
 l_Lean_IR_LogEntry_Lean_HasFormat = _init_l_Lean_IR_LogEntry_Lean_HasFormat();
lean::mark_persistent(l_Lean_IR_LogEntry_Lean_HasFormat);
 l_Lean_IR_tracePrefixOptionName = _init_l_Lean_IR_tracePrefixOptionName();
lean::mark_persistent(l_Lean_IR_tracePrefixOptionName);
 l___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___closed__1 = _init_l___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___closed__1();
lean::mark_persistent(l___private_init_lean_compiler_ir_compilerm_4__mkEntryArray___closed__1);
 l_Lean_SMap_empty___at_Lean_IR_mkDeclMapExtension___spec__1 = _init_l_Lean_SMap_empty___at_Lean_IR_mkDeclMapExtension___spec__1();
lean::mark_persistent(l_Lean_SMap_empty___at_Lean_IR_mkDeclMapExtension___spec__1);
 l_Lean_IR_mkDeclMapExtension___closed__1 = _init_l_Lean_IR_mkDeclMapExtension___closed__1();
lean::mark_persistent(l_Lean_IR_mkDeclMapExtension___closed__1);
w = l_Lean_IR_mkDeclMapExtension(w);
if (io_result_is_error(w)) return w;
 l_Lean_IR_declMapExt = io_result_get_value(w);
lean::mark_persistent(l_Lean_IR_declMapExt);
 l_Lean_IR_getDecl___closed__1 = _init_l_Lean_IR_getDecl___closed__1();
lean::mark_persistent(l_Lean_IR_getDecl___closed__1);
return w;
}
