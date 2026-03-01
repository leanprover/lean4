// Lean compiler output
// Module: Lean.Compiler.IR.EmitC
// Imports: public import Lean.Compiler.NameMangling public import Lean.Compiler.IR.EmitUtil public import Lean.Compiler.IR.NormIds public import Lean.Compiler.IR.SimpCase public import Lean.Compiler.ModPkgExt import Lean.Compiler.LCNF.Types import Lean.Compiler.ClosedTermCache import Lean.Compiler.LCNF.SimpleGroundExpr import Init.Omega import Init.While import Init.Data.Range.Polymorphic.Iterators import Lean.Runtime
#include <lean/lean.h>
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
static const lean_string_object l_Lean_IR_EmitC_leanMainFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "_lean_main"};
static const lean_object* l_Lean_IR_EmitC_leanMainFn___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_leanMainFn___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_EmitC_leanMainFn = (const lean_object*)&l_Lean_IR_EmitC_leanMainFn___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getEnv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getEnv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getModName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getModName___boxed(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkModuleInitializationFunctionName(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getModInitFn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getModInitFn___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_getDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unknown declaration '"};
static const lean_object* l_Lean_IR_EmitC_getDecl___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_getDecl___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_getDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_IR_EmitC_getDecl___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_getDecl___closed__1_value;
lean_object* l_Lean_IR_findEnvDecl(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emit___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitLn___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_IR_EmitC_emitLn___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitLn___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_EmitC_emitLns___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_EmitC_emitLns___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitLns___redArg___closed__0_value;
lean_object* l_EStateM_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_EmitC_emitLns___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_EmitC_emitLns___redArg___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitLns___redArg___closed__1_value;
lean_object* l_EStateM_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_EmitC_emitLns___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_EmitC_emitLns___redArg___closed__2 = (const lean_object*)&l_Lean_IR_EmitC_emitLns___redArg___closed__2_value;
lean_object* l_EStateM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_EmitC_emitLns___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_map, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_IR_EmitC_emitLns___redArg___closed__3 = (const lean_object*)&l_Lean_IR_EmitC_emitLns___redArg___closed__3_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitLns___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitLns___redArg___closed__3_value),((lean_object*)&l_Lean_IR_EmitC_emitLns___redArg___closed__0_value)}};
static const lean_object* l_Lean_IR_EmitC_emitLns___redArg___closed__4 = (const lean_object*)&l_Lean_IR_EmitC_emitLns___redArg___closed__4_value;
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_EmitC_emitLns___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_pure, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_IR_EmitC_emitLns___redArg___closed__5 = (const lean_object*)&l_Lean_IR_EmitC_emitLns___redArg___closed__5_value;
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_EmitC_emitLns___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_seqRight, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_IR_EmitC_emitLns___redArg___closed__6 = (const lean_object*)&l_Lean_IR_EmitC_emitLns___redArg___closed__6_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitLns___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitLns___redArg___closed__4_value),((lean_object*)&l_Lean_IR_EmitC_emitLns___redArg___closed__5_value),((lean_object*)&l_Lean_IR_EmitC_emitLns___redArg___closed__1_value),((lean_object*)&l_Lean_IR_EmitC_emitLns___redArg___closed__2_value),((lean_object*)&l_Lean_IR_EmitC_emitLns___redArg___closed__6_value)}};
static const lean_object* l_Lean_IR_EmitC_emitLns___redArg___closed__7 = (const lean_object*)&l_Lean_IR_EmitC_emitLns___redArg___closed__7_value;
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_EmitC_emitLns___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_bind, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_IR_EmitC_emitLns___redArg___closed__8 = (const lean_object*)&l_Lean_IR_EmitC_emitLns___redArg___closed__8_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitLns___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitLns___redArg___closed__7_value),((lean_object*)&l_Lean_IR_EmitC_emitLns___redArg___closed__8_value)}};
static const lean_object* l_Lean_IR_EmitC_emitLns___redArg___closed__9 = (const lean_object*)&l_Lean_IR_EmitC_emitLns___redArg___closed__9_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_once_cell_t l_Lean_IR_EmitC_emitLns___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_EmitC_emitLns___redArg___closed__10;
lean_object* l_List_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_argToCString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "x_"};
static const lean_object* l_Lean_IR_EmitC_argToCString___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_argToCString___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_argToCString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "lean_box(0)"};
static const lean_object* l_Lean_IR_EmitC_argToCString___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_argToCString___closed__1_value;
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_argToCString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_panic___at___00Lean_IR_EmitC_toCType_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_panic___at___00Lean_IR_EmitC_toCType_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_IR_EmitC_toCType_spec__0___closed__0_value;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_EmitC_toCType_spec__0(lean_object*);
static const lean_string_object l_Lean_IR_EmitC_toCType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "double"};
static const lean_object* l_Lean_IR_EmitC_toCType___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_toCType___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_toCType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "uint8_t"};
static const lean_object* l_Lean_IR_EmitC_toCType___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_toCType___closed__1_value;
static const lean_string_object l_Lean_IR_EmitC_toCType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "uint16_t"};
static const lean_object* l_Lean_IR_EmitC_toCType___closed__2 = (const lean_object*)&l_Lean_IR_EmitC_toCType___closed__2_value;
static const lean_string_object l_Lean_IR_EmitC_toCType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "uint32_t"};
static const lean_object* l_Lean_IR_EmitC_toCType___closed__3 = (const lean_object*)&l_Lean_IR_EmitC_toCType___closed__3_value;
static const lean_string_object l_Lean_IR_EmitC_toCType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "uint64_t"};
static const lean_object* l_Lean_IR_EmitC_toCType___closed__4 = (const lean_object*)&l_Lean_IR_EmitC_toCType___closed__4_value;
static const lean_string_object l_Lean_IR_EmitC_toCType___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "size_t"};
static const lean_object* l_Lean_IR_EmitC_toCType___closed__5 = (const lean_object*)&l_Lean_IR_EmitC_toCType___closed__5_value;
static const lean_string_object l_Lean_IR_EmitC_toCType___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "float"};
static const lean_object* l_Lean_IR_EmitC_toCType___closed__6 = (const lean_object*)&l_Lean_IR_EmitC_toCType___closed__6_value;
static const lean_string_object l_Lean_IR_EmitC_toCType___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Compiler.IR.EmitC"};
static const lean_object* l_Lean_IR_EmitC_toCType___closed__7 = (const lean_object*)&l_Lean_IR_EmitC_toCType___closed__7_value;
static const lean_string_object l_Lean_IR_EmitC_toCType___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.IR.EmitC.toCType"};
static const lean_object* l_Lean_IR_EmitC_toCType___closed__8 = (const lean_object*)&l_Lean_IR_EmitC_toCType___closed__8_value;
static const lean_string_object l_Lean_IR_EmitC_toCType___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "not implemented yet"};
static const lean_object* l_Lean_IR_EmitC_toCType___closed__9 = (const lean_object*)&l_Lean_IR_EmitC_toCType___closed__9_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_IR_EmitC_toCType___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_EmitC_toCType___closed__10;
static lean_once_cell_t l_Lean_IR_EmitC_toCType___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_EmitC_toCType___closed__11;
static const lean_string_object l_Lean_IR_EmitC_toCType___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "lean_object*"};
static const lean_object* l_Lean_IR_EmitC_toCType___closed__12 = (const lean_object*)&l_Lean_IR_EmitC_toCType___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCType___boxed(lean_object*);
uint32_t l_Nat_digitChar(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toHexDigit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toHexDigit___boxed(lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\x"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\\?"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\\""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\\\"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\t"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__4_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\r"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\n"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__6_value;
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_quoteString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l_Lean_IR_EmitC_quoteString___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_quoteString___closed__0_value;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_quoteString(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_throwInvalidExportName___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid export name '"};
static const lean_object* l_Lean_IR_EmitC_throwInvalidExportName___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_throwInvalidExportName___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwInvalidExportName___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwInvalidExportName(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwInvalidExportName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_toCName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "main"};
static const lean_object* l_Lean_IR_EmitC_toCName___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_toCName___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_IR_EmitC_toCName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_EmitC_toCName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 14, 67, 68, 149, 142, 182, 10)}};
static const lean_object* l_Lean_IR_EmitC_toCName___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_toCName___closed__1_value;
lean_object* lean_get_export_name_for(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_get_symbol_stem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCName(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_toCInitName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_init_"};
static const lean_object* l_Lean_IR_EmitC_toCInitName___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_toCInitName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCInitName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCInitName(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_ctorScalarSizeStr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "sizeof(size_t)*"};
static const lean_object* l_Lean_IR_EmitC_ctorScalarSizeStr___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_ctorScalarSizeStr___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_ctorScalarSizeStr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " + "};
static const lean_object* l_Lean_IR_EmitC_ctorScalarSizeStr___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_ctorScalarSizeStr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_ctorScalarSizeStr(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_value"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueName___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueName___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getSimpleGroundExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_findValueDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_findValueDecl(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxValueName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_aux_"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxValueName___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxValueName___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxValueName(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "static const "};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " = "};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__2 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__3 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__3_value;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "((lean_object*)(((size_t)("};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ") << 1) | 1))"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "((lean_object*)&"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__2 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__3 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "{.m_rc = 0, .m_cs_sz = "};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", .m_other = "};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ", .m_tag = "};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__2 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__3 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkCtorHeader_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkCtorHeader_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkCtorHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "sizeof(lean_ctor_object) + sizeof(void*)*"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkCtorHeader___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkCtorHeader___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkCtorHeader(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__0;
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__1;
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__2;
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__3;
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__4;
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__5;
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__6;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "(lean_object*)(size_t)("};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ULL)"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__2___closed__1_value;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "LEAN_SCALAR_PTR_LITERAL("};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1_value;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern uint8_t l_instInhabitedUInt8;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "_private.Lean.Compiler.IR.EmitC.0.Lean.IR.EmitC.emitGroundDecl.compileCtor"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "assertion violation: scalarArgs.size % 8 == 0\n    "};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__2;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__3 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "{.m_header = "};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__4 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__4_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", .m_objs = {"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__5 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "}}"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__6 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__6_value;
lean_object* lean_array_get_size(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "_private.Lean.Compiler.IR.EmitC.0.Lean.IR.EmitC.emitGroundDecl.groundNameMkStrToCLit"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "assertion violation: args.size > 0\n    "};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__2;
extern uint64_t l_instInhabitedUInt64;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__3___boxed__const__1;
static lean_once_cell_t l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__3;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "lean_ctor_object"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__4 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__4_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__5 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__6 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__6_value;
static lean_once_cell_t l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__7;
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_uint64ToByteArrayLE(uint64_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueCLit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueCLit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueCLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueCLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__0;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "lean_string_object"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__2;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ", .m_size = "};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__3 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__3_value;
static lean_once_cell_t l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__4;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = ", .m_capacity = "};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__5 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ", .m_length = "};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__6 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__6_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ", .m_data = "};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__7 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__7_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "sizeof(lean_closure_object) + sizeof(void*)*"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__8 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__8_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "(void*)"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__9 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__9_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "lean_closure_object"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__10 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__10_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ", .m_fun = "};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__11 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__11_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", .m_arity = "};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__12 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__12_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = ", .m_num_fixed = "};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__13 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__13_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "} }"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__14 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__14_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "sizeof(lean_array_object) + sizeof(void*)*"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__15 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__15_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "lean_array_object"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__16 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__16_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", .m_data = {"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__17 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__17_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "sizeof(lean_sarray_object) + "};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__18 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__18_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "lean_sarray_object"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__19 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__19_value;
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_IR_Decl_params(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGround___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = " const lean_object* "};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGround___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGround___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGround___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = " = (const lean_object*)&"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGround___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGround___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGround___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "LEAN_EXPORT"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGround___closed__2 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGround___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGround___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "static"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGround___closed__3 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGround___closed__3_value;
lean_object* l_Lean_IR_Decl_name(lean_object*);
uint8_t l_Lean_isClosedTermName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGround(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGround___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_EmitC_emitGroundDecl_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitGroundDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.IR.EmitC.emitGroundDecl"};
static const lean_object* l_Lean_IR_EmitC_emitGroundDecl___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitGroundDecl___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitGroundDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_IR_EmitC_emitGroundDecl___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitGroundDecl___closed__1_value;
static lean_once_cell_t l_Lean_IR_EmitC_emitGroundDecl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_EmitC_emitGroundDecl___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitGroundDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitGroundDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_toTokenName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_once"};
static const lean_object* l_Lean_IR_EmitC_toTokenName___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_toTokenName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toTokenName(lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitFnClosedDecl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "static lean_once_cell_t "};
static const lean_object* l_Lean_IR_EmitC_emitFnClosedDecl___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitFnClosedDecl___redArg___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitFnClosedDecl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = " = LEAN_ONCE_CELL_INITIALIZER;"};
static const lean_object* l_Lean_IR_EmitC_emitFnClosedDecl___redArg___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitFnClosedDecl___redArg___closed__1_value;
static const lean_string_object l_Lean_IR_EmitC_emitFnClosedDecl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "static "};
static const lean_object* l_Lean_IR_EmitC_emitFnClosedDecl___redArg___closed__2 = (const lean_object*)&l_Lean_IR_EmitC_emitFnClosedDecl___redArg___closed__2_value;
lean_object* l_Lean_IR_Decl_resultType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnClosedDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnClosedDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnClosedDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnClosedDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__1(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_IR_IRType_isErased(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__2(lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_IR_IRType_isVoid(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitFnDeclAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitFnDeclAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitFnDeclAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "lean_object**"};
static const lean_object* l_Lean_IR_EmitC_emitFnDeclAux___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitFnDeclAux___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitFnDeclAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_IR_EmitC_emitFnDeclAux___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitFnDeclAux___closed__1_value;
static const lean_array_object l_Lean_IR_EmitC_emitFnDeclAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_IR_EmitC_emitFnDeclAux___closed__2 = (const lean_object*)&l_Lean_IR_EmitC_emitFnDeclAux___closed__2_value;
static const lean_string_object l_Lean_IR_EmitC_emitFnDeclAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "LEAN_EXPORT "};
static const lean_object* l_Lean_IR_EmitC_emitFnDeclAux___closed__3 = (const lean_object*)&l_Lean_IR_EmitC_emitFnDeclAux___closed__3_value;
static const lean_string_object l_Lean_IR_EmitC_emitFnDeclAux___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "extern "};
static const lean_object* l_Lean_IR_EmitC_emitFnDeclAux___closed__4 = (const lean_object*)&l_Lean_IR_EmitC_emitFnDeclAux___closed__4_value;
extern lean_object* l_Lean_closureMaxArgs;
uint8_t l_Lean_Compiler_LCNF_isBoxedName(lean_object*);
uint8_t l_Lean_isExternC(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Compiler_LCNF_isSimpleGroundDecl(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitFnDeclAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitFnDeclAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDecl(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitExternDeclAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitExternDeclAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_IR_EmitC_emitFnDecls_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_IR_EmitC_emitFnDecls_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDecls_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "c"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDecls_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDecls_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDecls_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDecls_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(38, 183, 255, 58, 84, 31, 100, 5)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDecls_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDecls_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDecls_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getExternNameFor(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDecls_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_getDecls(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_IR_collectUsedDecls(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDecls(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_IR_EmitC_emitMainFn_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_IR_EmitC_emitMainFn_spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedConstantInfo_default;
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_EmitC_emitMainFn_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "  lean_dec_ref(res);"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "  return ret;"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__1_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "} else {"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__2 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__2_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "  lean_io_result_show_error(res);"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__3 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__3_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "  return 1;"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__4 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__4_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "lean_finalize_task_manager();"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__5 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__5_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "  int ret = "};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__6 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__6_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__7 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__7_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitMainFn___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__7_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__8 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__8_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitMainFn___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__8_value)}};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__9 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__9_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "0;"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__10 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__10_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "lean_unbox_uint32(lean_io_result_get_value(res));"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__11 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__11_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__12 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__12_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__13 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__13_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__14 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__14_value;
static lean_once_cell_t l_Lean_IR_EmitC_emitMainFn___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__15;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "res = "};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__16 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__16_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "(1 /* builtin */);"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__17 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__17_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "lean_set_panic_messages(true);"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__18 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__18_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "lean_io_mark_end_initialization();"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__19 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__19_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "if (lean_io_result_is_ok(res)) {"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__20 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__20_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "lean_dec_ref(res);"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__21 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__21_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "lean_init_task_manager();"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__22 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__22_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitMainFn___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__23 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__23_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitMainFn___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__21_value),((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__23_value)}};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__24 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__24_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitMainFn___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__20_value),((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__24_value)}};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__25 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__25_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitMainFn___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__19_value),((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__25_value)}};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__26 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__26_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "res = _lean_main();"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__27 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__27_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "in = lean_box(0);"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__28 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__28_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "int i = argc;"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__29 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__29_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while (i > 1) {"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__30 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__30_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " lean_object* n;"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__31 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__31_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " i--;"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__32 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__32_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 100, .m_capacity = 100, .m_length = 99, .m_data = " n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__33 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__33_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " in = n;"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__34 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__34_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitMainFn___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__35 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__35_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitMainFn___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__34_value),((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__35_value)}};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__36 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__36_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitMainFn___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__33_value),((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__36_value)}};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__37 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__37_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitMainFn___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__32_value),((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__37_value)}};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__38 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__38_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitMainFn___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__31_value),((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__38_value)}};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__39 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__39_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitMainFn___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__30_value),((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__39_value)}};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__40 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__40_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitMainFn___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__29_value),((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__40_value)}};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__41 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__41_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitMainFn___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__28_value),((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__41_value)}};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__42 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__42_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "res = _lean_main(in);"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__43 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__43_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "lean_set_panic_messages(false);"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__44 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__44_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 268, .m_capacity = 268, .m_length = 267, .m_data = "\n  #if defined(WIN32) || defined(_WIN32)\n  #include <windows.h>\n  #endif\n\n  int main(int argc, char ** argv) {\n  #if defined(WIN32) || defined(_WIN32)\n  SetErrorMode(SEM_FAILCRITICALERRORS);\n  SetConsoleOutputCP(CP_UTF8);\n  #endif\n  lean_object* in; lean_object* res;"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__45 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__45_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "argv = lean_setup_args(argc, argv);"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__46 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__46_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "lean_initialize_runtime_module();"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__47 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__47_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "lean_initialize();"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__48 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__48_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "invalid main function, incorrect arity when generating code"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__49 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__49_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__50 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__50_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitMainFn___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__50_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__51 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__51_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "char ** lean_setup_args(int argc, char ** argv);"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__52 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__52_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "void lean_initialize_runtime_module();"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__53 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__53_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "void lean_initialize();"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__54 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__54_value;
static const lean_string_object l_Lean_IR_EmitC_emitMainFn___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "function declaration expected"};
static const lean_object* l_Lean_IR_EmitC_emitMainFn___closed__55 = (const lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__55_value;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Expr_getForallBody(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_header(lean_object*);
uint8_t l_Lean_IR_usesModuleFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_EmitC_hasMainFn___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_hasMainFn___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_IR_EmitC_hasMainFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_EmitC_hasMainFn___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_EmitC_hasMainFn___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_hasMainFn___closed__0_value;
uint8_t l_List_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_hasMainFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFnIfNeeded(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "import "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "all "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "meta "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "public "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitFileHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "#include <lean/lean.h>"};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitFileHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "#if defined(__clang__)"};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__1_value;
static const lean_string_object l_Lean_IR_EmitC_emitFileHeader___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "#pragma clang diagnostic ignored \"-Wunused-parameter\""};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__2 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__2_value;
static const lean_string_object l_Lean_IR_EmitC_emitFileHeader___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "#pragma clang diagnostic ignored \"-Wunused-label\""};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__3 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__3_value;
static const lean_string_object l_Lean_IR_EmitC_emitFileHeader___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "#elif defined(__GNUC__) && !defined(__CLANG__)"};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__4 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__4_value;
static const lean_string_object l_Lean_IR_EmitC_emitFileHeader___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "#pragma GCC diagnostic ignored \"-Wunused-parameter\""};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__5 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__5_value;
static const lean_string_object l_Lean_IR_EmitC_emitFileHeader___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "#pragma GCC diagnostic ignored \"-Wunused-label\""};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__6 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__6_value;
static const lean_string_object l_Lean_IR_EmitC_emitFileHeader___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "#pragma GCC diagnostic ignored \"-Wunused-but-set-variable\""};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__7 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__7_value;
static const lean_string_object l_Lean_IR_EmitC_emitFileHeader___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "#endif"};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__8 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__8_value;
static const lean_string_object l_Lean_IR_EmitC_emitFileHeader___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "#ifdef __cplusplus"};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__9 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__9_value;
static const lean_string_object l_Lean_IR_EmitC_emitFileHeader___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extern \"C\" {"};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__10 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__10_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitFileHeader___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__11 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__11_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitFileHeader___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__10_value),((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__11_value)}};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__12 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__12_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitFileHeader___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__9_value),((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__12_value)}};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__13 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__13_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitFileHeader___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__8_value),((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__13_value)}};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__14 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__14_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitFileHeader___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__7_value),((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__14_value)}};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__15 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__15_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitFileHeader___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__6_value),((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__15_value)}};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__16 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__16_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitFileHeader___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__5_value),((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__16_value)}};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__17 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__17_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitFileHeader___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__4_value),((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__17_value)}};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__18 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__18_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitFileHeader___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__3_value),((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__18_value)}};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__19 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__19_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitFileHeader___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__2_value),((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__19_value)}};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__20 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__20_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitFileHeader___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__1_value),((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__20_value)}};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__21 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__21_value;
static const lean_string_object l_Lean_IR_EmitC_emitFileHeader___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "// Lean compiler output"};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__22 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__22_value;
static const lean_string_object l_Lean_IR_EmitC_emitFileHeader___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "// Module: "};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__23 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__23_value;
static const lean_string_object l_Lean_IR_EmitC_emitFileHeader___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "// Imports:"};
static const lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__24 = (const lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__24_value;
lean_object* l_Lean_Environment_imports(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileHeader(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_IR_EmitC_emitFileFooter___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__3_value),((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__11_value)}};
static const lean_object* l_Lean_IR_EmitC_emitFileFooter___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitFileFooter___redArg___closed__0_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitFileFooter___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitFileHeader___closed__9_value),((lean_object*)&l_Lean_IR_EmitC_emitFileFooter___redArg___closed__0_value)}};
static const lean_object* l_Lean_IR_EmitC_emitFileFooter___redArg___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitFileFooter___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileFooter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileFooter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileFooter___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_throwUnknownVar___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknown variable '"};
static const lean_object* l_Lean_IR_EmitC_throwUnknownVar___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_throwUnknownVar___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwUnknownVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwUnknownVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwUnknownVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_instBEqJoinPointId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
uint64_t l_Lean_IR_instHashableJoinPointId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_getJPParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknown join point"};
static const lean_object* l_Lean_IR_EmitC_getJPParams___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_getJPParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getJPParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getJPParams___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_declareVar___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "; "};
static const lean_object* l_Lean_IR_EmitC_declareVar___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_declareVar___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_declareParams_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_declareParams_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareParams___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_declareParams_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_declareParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_isTailCallTo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVars(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitTag___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "lean_obj_tag("};
static const lean_object* l_Lean_IR_EmitC_emitTag___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitTag___redArg___closed__0_value;
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTag___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTag___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTag(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_IR_Alt_body(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isIf(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isIf___boxed(lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitInc___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ");"};
static const lean_object* l_Lean_IR_EmitC_emitInc___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitInc___redArg___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitInc___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lean_inc_ref_n"};
static const lean_object* l_Lean_IR_EmitC_emitInc___redArg___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitInc___redArg___closed__1_value;
static const lean_string_object l_Lean_IR_EmitC_emitInc___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "lean_inc_ref"};
static const lean_object* l_Lean_IR_EmitC_emitInc___redArg___closed__2 = (const lean_object*)&l_Lean_IR_EmitC_emitInc___redArg___closed__2_value;
static const lean_string_object l_Lean_IR_EmitC_emitInc___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "lean_inc_n"};
static const lean_object* l_Lean_IR_EmitC_emitInc___redArg___closed__3 = (const lean_object*)&l_Lean_IR_EmitC_emitInc___redArg___closed__3_value;
static const lean_string_object l_Lean_IR_EmitC_emitInc___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_inc"};
static const lean_object* l_Lean_IR_EmitC_emitInc___redArg___closed__4 = (const lean_object*)&l_Lean_IR_EmitC_emitInc___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInc___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInc(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitDec___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "lean_dec_ref"};
static const lean_object* l_Lean_IR_EmitC_emitDec___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitDec___redArg___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitDec___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_dec"};
static const lean_object* l_Lean_IR_EmitC_emitDec___redArg___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitDec___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDec___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDec___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDec(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitDel___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "lean_del_object("};
static const lean_object* l_Lean_IR_EmitC_emitDel___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitDel___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDel___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDel___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitSetTag___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "lean_ctor_set_tag("};
static const lean_object* l_Lean_IR_EmitC_emitSetTag___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitSetTag___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSetTag___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSetTag(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSetTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitSet___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lean_ctor_set("};
static const lean_object* l_Lean_IR_EmitC_emitSet___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitSet___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitOffset___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "sizeof(void*)*"};
static const lean_object* l_Lean_IR_EmitC_emitOffset___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitOffset___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitOffset___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitOffset(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitUSet___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "lean_ctor_set_usize("};
static const lean_object* l_Lean_IR_EmitC_emitUSet___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitUSet___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitSSet___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "lean_ctor_set_float"};
static const lean_object* l_Lean_IR_EmitC_emitSSet___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitSSet___redArg___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitSSet___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "lean_ctor_set_float32"};
static const lean_object* l_Lean_IR_EmitC_emitSSet___redArg___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitSSet___redArg___closed__1_value;
static const lean_string_object l_Lean_IR_EmitC_emitSSet___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "lean_ctor_set_uint8"};
static const lean_object* l_Lean_IR_EmitC_emitSSet___redArg___closed__2 = (const lean_object*)&l_Lean_IR_EmitC_emitSSet___redArg___closed__2_value;
static const lean_string_object l_Lean_IR_EmitC_emitSSet___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "lean_ctor_set_uint16"};
static const lean_object* l_Lean_IR_EmitC_emitSSet___redArg___closed__3 = (const lean_object*)&l_Lean_IR_EmitC_emitSSet___redArg___closed__3_value;
static const lean_string_object l_Lean_IR_EmitC_emitSSet___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "lean_ctor_set_uint32"};
static const lean_object* l_Lean_IR_EmitC_emitSSet___redArg___closed__4 = (const lean_object*)&l_Lean_IR_EmitC_emitSSet___redArg___closed__4_value;
static const lean_string_object l_Lean_IR_EmitC_emitSSet___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "lean_ctor_set_uint64"};
static const lean_object* l_Lean_IR_EmitC_emitSSet___redArg___closed__5 = (const lean_object*)&l_Lean_IR_EmitC_emitSSet___redArg___closed__5_value;
static const lean_string_object l_Lean_IR_EmitC_emitSSet___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "invalid instruction"};
static const lean_object* l_Lean_IR_EmitC_emitSSet___redArg___closed__6 = (const lean_object*)&l_Lean_IR_EmitC_emitSSet___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSSet___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitJmp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "invalid goto"};
static const lean_object* l_Lean_IR_EmitC_emitJmp___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitJmp___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitJmp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "goto "};
static const lean_object* l_Lean_IR_EmitC_emitJmp___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitJmp___closed__1_value;
static const lean_string_object l_Lean_IR_EmitC_emitJmp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "block_"};
static const lean_object* l_Lean_IR_EmitC_emitJmp___closed__2 = (const lean_object*)&l_Lean_IR_EmitC_emitJmp___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitJmp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitJmp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLhs___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLhs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLhs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArgs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorScalarSize___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorScalarSize(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorScalarSize___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitAllocCtor___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "lean_alloc_ctor("};
static const lean_object* l_Lean_IR_EmitC_emitAllocCtor___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitAllocCtor___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitAllocCtor___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitAllocCtor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitAllocCtor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorSetArgs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorSetArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitCtor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "lean_box("};
static const lean_object* l_Lean_IR_EmitC_emitCtor___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitCtor___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = " lean_ctor_release("};
static const lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitReset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "if (lean_is_exclusive("};
static const lean_object* l_Lean_IR_EmitC_emitReset___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitReset___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitReset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ")) {"};
static const lean_object* l_Lean_IR_EmitC_emitReset___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitReset___closed__1_value;
static const lean_string_object l_Lean_IR_EmitC_emitReset___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = " lean_dec_ref("};
static const lean_object* l_Lean_IR_EmitC_emitReset___closed__2 = (const lean_object*)&l_Lean_IR_EmitC_emitReset___closed__2_value;
static const lean_string_object l_Lean_IR_EmitC_emitReset___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "lean_box(0);"};
static const lean_object* l_Lean_IR_EmitC_emitReset___closed__3 = (const lean_object*)&l_Lean_IR_EmitC_emitReset___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitReuse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "if (lean_is_scalar("};
static const lean_object* l_Lean_IR_EmitC_emitReuse___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitReuse___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitReuse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = " lean_ctor_set_tag("};
static const lean_object* l_Lean_IR_EmitC_emitReuse___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitReuse___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReuse(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitProj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lean_ctor_get("};
static const lean_object* l_Lean_IR_EmitC_emitProj___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitProj___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitProj___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitUProj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "lean_ctor_get_usize("};
static const lean_object* l_Lean_IR_EmitC_emitUProj___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitUProj___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUProj___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitSProj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "lean_ctor_get_float"};
static const lean_object* l_Lean_IR_EmitC_emitSProj___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitSProj___redArg___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitSProj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "lean_ctor_get_float32"};
static const lean_object* l_Lean_IR_EmitC_emitSProj___redArg___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitSProj___redArg___closed__1_value;
static const lean_string_object l_Lean_IR_EmitC_emitSProj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "lean_ctor_get_uint8"};
static const lean_object* l_Lean_IR_EmitC_emitSProj___redArg___closed__2 = (const lean_object*)&l_Lean_IR_EmitC_emitSProj___redArg___closed__2_value;
static const lean_string_object l_Lean_IR_EmitC_emitSProj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "lean_ctor_get_uint16"};
static const lean_object* l_Lean_IR_EmitC_emitSProj___redArg___closed__3 = (const lean_object*)&l_Lean_IR_EmitC_emitSProj___redArg___closed__3_value;
static const lean_string_object l_Lean_IR_EmitC_emitSProj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "lean_ctor_get_uint32"};
static const lean_object* l_Lean_IR_EmitC_emitSProj___redArg___closed__4 = (const lean_object*)&l_Lean_IR_EmitC_emitSProj___redArg___closed__4_value;
static const lean_string_object l_Lean_IR_EmitC_emitSProj___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "lean_ctor_get_uint64"};
static const lean_object* l_Lean_IR_EmitC_emitSProj___redArg___closed__5 = (const lean_object*)&l_Lean_IR_EmitC_emitSProj___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSProj___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSProj___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_IR_EmitC_toStringArgs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toStringArgs(lean_object*);
extern lean_object* l_Lean_IR_instInhabitedParam_default;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSimpleExternalCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSimpleExternalCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitExternCall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "failed to emit extern application '"};
static const lean_object* l_Lean_IR_EmitC_emitExternCall___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitExternCall___closed__0_value;
lean_object* l_Lean_getExternEntryFor(lean_object*, lean_object*);
lean_object* l_Lean_expandExternPattern(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitExternCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitExternCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "(&"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ", &"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "lean_obj_once"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__2 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "lean_float_once"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__3 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "lean_float32_once"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__4 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__4_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "lean_uint8_once"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__5 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "lean_uint16_once"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__6 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__6_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "lean_uint32_once"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__7 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__7_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "lean_uint64_once"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__8 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__8_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "lean_usize_once"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__9 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__9_value;
static const lean_string_object l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "failed to emit closed term read for '"};
static const lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__10 = (const lean_object*)&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitLeanFunReference___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "((lean_object*)("};
static const lean_object* l_Lean_IR_EmitC_emitLeanFunReference___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitLeanFunReference___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitLeanFunReference___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "))"};
static const lean_object* l_Lean_IR_EmitC_emitLeanFunReference___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitLeanFunReference___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLeanFunReference(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLeanFunReference___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFullApp_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFullApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_IR_EmitC_emitFullApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_IR_EmitC_emitFullApp___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitFullApp___closed__0_value;
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFullApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFullApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "lean_closure_set("};
static const lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitPartialApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "lean_alloc_closure((void*)("};
static const lean_object* l_Lean_IR_EmitC_emitPartialApp___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitPartialApp___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitPartialApp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "), "};
static const lean_object* l_Lean_IR_EmitC_emitPartialApp___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitPartialApp___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitPartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitPartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "lean_apply_"};
static const lean_object* l_Lean_IR_EmitC_emitApp___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitApp___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitApp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "{ lean_object* _aargs[] = {"};
static const lean_object* l_Lean_IR_EmitC_emitApp___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitApp___closed__1_value;
static const lean_string_object l_Lean_IR_EmitC_emitApp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "};"};
static const lean_object* l_Lean_IR_EmitC_emitApp___closed__2 = (const lean_object*)&l_Lean_IR_EmitC_emitApp___closed__2_value;
static const lean_string_object l_Lean_IR_EmitC_emitApp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "lean_apply_m("};
static const lean_object* l_Lean_IR_EmitC_emitApp___closed__3 = (const lean_object*)&l_Lean_IR_EmitC_emitApp___closed__3_value;
static const lean_string_object l_Lean_IR_EmitC_emitApp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ", _aargs); }"};
static const lean_object* l_Lean_IR_EmitC_emitApp___closed__4 = (const lean_object*)&l_Lean_IR_EmitC_emitApp___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitBoxFn___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lean_box_usize"};
static const lean_object* l_Lean_IR_EmitC_emitBoxFn___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitBoxFn___redArg___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitBoxFn___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "lean_box_uint32"};
static const lean_object* l_Lean_IR_EmitC_emitBoxFn___redArg___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitBoxFn___redArg___closed__1_value;
static const lean_string_object l_Lean_IR_EmitC_emitBoxFn___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "lean_box_uint64"};
static const lean_object* l_Lean_IR_EmitC_emitBoxFn___redArg___closed__2 = (const lean_object*)&l_Lean_IR_EmitC_emitBoxFn___redArg___closed__2_value;
static const lean_string_object l_Lean_IR_EmitC_emitBoxFn___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lean_box_float"};
static const lean_object* l_Lean_IR_EmitC_emitBoxFn___redArg___closed__3 = (const lean_object*)&l_Lean_IR_EmitC_emitBoxFn___redArg___closed__3_value;
static const lean_string_object l_Lean_IR_EmitC_emitBoxFn___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "lean_box_float32"};
static const lean_object* l_Lean_IR_EmitC_emitBoxFn___redArg___closed__4 = (const lean_object*)&l_Lean_IR_EmitC_emitBoxFn___redArg___closed__4_value;
static const lean_string_object l_Lean_IR_EmitC_emitBoxFn___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_box"};
static const lean_object* l_Lean_IR_EmitC_emitBoxFn___redArg___closed__5 = (const lean_object*)&l_Lean_IR_EmitC_emitBoxFn___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBoxFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBoxFn___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBoxFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBoxFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBox___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBox___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBox(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBox___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_getUnboxOpName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnbox___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnbox___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnbox(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnbox___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitIsShared___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "!lean_is_exclusive("};
static const lean_object* l_Lean_IR_EmitC_emitIsShared___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitIsShared___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIsShared___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIsShared(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIsShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitNumLit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ULL"};
static const lean_object* l_Lean_IR_EmitC_emitNumLit___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitNumLit___redArg___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitNumLit___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "((size_t)"};
static const lean_object* l_Lean_IR_EmitC_emitNumLit___redArg___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitNumLit___redArg___closed__1_value;
static const lean_string_object l_Lean_IR_EmitC_emitNumLit___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "lean_cstr_to_nat(\""};
static const lean_object* l_Lean_IR_EmitC_emitNumLit___redArg___closed__2 = (const lean_object*)&l_Lean_IR_EmitC_emitNumLit___redArg___closed__2_value;
static const lean_string_object l_Lean_IR_EmitC_emitNumLit___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\")"};
static const lean_object* l_Lean_IR_EmitC_emitNumLit___redArg___closed__3 = (const lean_object*)&l_Lean_IR_EmitC_emitNumLit___redArg___closed__3_value;
static const lean_string_object l_Lean_IR_EmitC_emitNumLit___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "lean_unsigned_to_nat("};
static const lean_object* l_Lean_IR_EmitC_emitNumLit___redArg___closed__4 = (const lean_object*)&l_Lean_IR_EmitC_emitNumLit___redArg___closed__4_value;
static const lean_string_object l_Lean_IR_EmitC_emitNumLit___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "u)"};
static const lean_object* l_Lean_IR_EmitC_emitNumLit___redArg___closed__5 = (const lean_object*)&l_Lean_IR_EmitC_emitNumLit___redArg___closed__5_value;
uint8_t l_Lean_IR_instBEqIRType_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitNumLit___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitNumLit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitNumLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitLit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "lean_mk_string_unchecked("};
static const lean_object* l_Lean_IR_EmitC_emitLit___redArg___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitLit___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitVDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_instBEqVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isTailCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isTailCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_EmitC_paramEqArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_paramEqArg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedArg_default;
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_EmitC_overwriteParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_overwriteParam___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitTailCall_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitTailCall_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " _tmp_"};
static const lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " = _tmp_"};
static const lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitTailCall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "goto _start;"};
static const lean_object* l_Lean_IR_EmitC_emitTailCall___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitTailCall___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitTailCall___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean_IR_EmitC_emitTailCall___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitTailCall___closed__1_value;
static const lean_string_object l_Lean_IR_EmitC_emitTailCall___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "invalid tail call"};
static const lean_object* l_Lean_IR_EmitC_emitTailCall___closed__2 = (const lean_object*)&l_Lean_IR_EmitC_emitTailCall___closed__2_value;
static const lean_array_object l_Lean_IR_EmitC_emitTailCall___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_IR_EmitC_emitTailCall___closed__3 = (const lean_object*)&l_Lean_IR_EmitC_emitTailCall___closed__3_value;
static const lean_string_object l_Lean_IR_EmitC_emitTailCall___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "bug at emitTailCall"};
static const lean_object* l_Lean_IR_EmitC_emitTailCall___closed__4 = (const lean_object*)&l_Lean_IR_EmitC_emitTailCall___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTailCall(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTailCall___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitIf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "if ("};
static const lean_object* l_Lean_IR_EmitC_emitIf___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitIf___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitIf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " == "};
static const lean_object* l_Lean_IR_EmitC_emitIf___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitIf___closed__1_value;
static const lean_string_object l_Lean_IR_EmitC_emitIf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l_Lean_IR_EmitC_emitIf___closed__2 = (const lean_object*)&l_Lean_IR_EmitC_emitIf___closed__2_value;
static const lean_string_object l_Lean_IR_EmitC_emitCase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "switch ("};
static const lean_object* l_Lean_IR_EmitC_emitCase___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitCase___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitCase___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ") {"};
static const lean_object* l_Lean_IR_EmitC_emitCase___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitCase___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "case "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitJPs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_IR_EmitC_emitJPs___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitJPs___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "default: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnBody(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ensureHasDefault(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "return "};
static const lean_object* l_Lean_IR_EmitC_emitBlock___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitBlock___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitBlock___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "lean_internal_panic_unreachable();"};
static const lean_object* l_Lean_IR_EmitC_emitBlock___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitBlock___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBlock(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitJPs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "lean_object* "};
static const lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " = _args["};
static const lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "];"};
static const lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitDeclAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_start:"};
static const lean_object* l_Lean_IR_EmitC_emitDeclAux___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitDeclAux___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitDeclAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " {"};
static const lean_object* l_Lean_IR_EmitC_emitDeclAux___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitDeclAux___closed__1_value;
static const lean_string_object l_Lean_IR_EmitC_emitDeclAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "lean_object** _args"};
static const lean_object* l_Lean_IR_EmitC_emitDeclAux___closed__2 = (const lean_object*)&l_Lean_IR_EmitC_emitDeclAux___closed__2_value;
static const lean_string_object l_Lean_IR_EmitC_emitDeclAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "(void)"};
static const lean_object* l_Lean_IR_EmitC_emitDeclAux___closed__3 = (const lean_object*)&l_Lean_IR_EmitC_emitDeclAux___closed__3_value;
lean_object* l_Lean_IR_mkVarJPMaps(lean_object*);
uint8_t l_Lean_hasInitAttr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "\ncompiling:\n"};
static const lean_object* l_Lean_IR_EmitC_emitDecl___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitDecl___closed__0_value;
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
lean_object* l_Lean_IR_declToString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitFns_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFns(lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitMarkPersistent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "lean_mark_persistent("};
static const lean_object* l_Lean_IR_EmitC_emitMarkPersistent___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitMarkPersistent___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMarkPersistent(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMarkPersistent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_withErrRet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "if (lean_io_result_is_error(res)) return res;"};
static const lean_object* l_Lean_IR_EmitC_withErrRet___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_withErrRet___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_withErrRet(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitDeclInit___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "()"};
static const lean_object* l_Lean_IR_EmitC_emitDeclInit___lam__0___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitDeclInit___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclInit___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclInit___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitDeclInit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = " = lean_io_result_get_value(res);"};
static const lean_object* l_Lean_IR_EmitC_emitDeclInit___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitDeclInit___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitDeclInit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "(lean_io_result_get_value(res));"};
static const lean_object* l_Lean_IR_EmitC_emitDeclInit___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitDeclInit___closed__1_value;
static const lean_string_object l_Lean_IR_EmitC_emitDeclInit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "();"};
static const lean_object* l_Lean_IR_EmitC_emitDeclInit___closed__2 = (const lean_object*)&l_Lean_IR_EmitC_emitDeclInit___closed__2_value;
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
lean_object* lean_get_init_fn_name_for(lean_object*, lean_object*);
uint8_t l_Lean_isIOUnitInitFn(lean_object*, lean_object*);
lean_object* l_Lean_getBuiltinInitFnNameFor_x3f(lean_object*, lean_object*);
uint8_t l_Lean_isIOUnitBuiltinInitFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclInit(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclInit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_IR_EmitC_emitInitFn_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqIRPhases_beq(uint8_t, uint8_t);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_IR_EmitC_emitInitFn_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "(builtin)"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "(uint8_t builtin);"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "(internal) import without module index"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdx_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModulePackageByIdx_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitInitFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "_G_"};
static const lean_object* l_Lean_IR_EmitC_emitInitFn___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitInitFn___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitInitFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "initialized"};
static const lean_object* l_Lean_IR_EmitC_emitInitFn___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitInitFn___closed__1_value;
static const lean_string_object l_Lean_IR_EmitC_emitInitFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "static bool "};
static const lean_object* l_Lean_IR_EmitC_emitInitFn___closed__2 = (const lean_object*)&l_Lean_IR_EmitC_emitInitFn___closed__2_value;
static const lean_string_object l_Lean_IR_EmitC_emitInitFn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " = false;"};
static const lean_object* l_Lean_IR_EmitC_emitInitFn___closed__3 = (const lean_object*)&l_Lean_IR_EmitC_emitInitFn___closed__3_value;
static const lean_string_object l_Lean_IR_EmitC_emitInitFn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "LEAN_EXPORT lean_object* "};
static const lean_object* l_Lean_IR_EmitC_emitInitFn___closed__4 = (const lean_object*)&l_Lean_IR_EmitC_emitInitFn___closed__4_value;
static const lean_string_object l_Lean_IR_EmitC_emitInitFn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "(uint8_t builtin) {"};
static const lean_object* l_Lean_IR_EmitC_emitInitFn___closed__5 = (const lean_object*)&l_Lean_IR_EmitC_emitInitFn___closed__5_value;
static const lean_string_object l_Lean_IR_EmitC_emitInitFn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "lean_object * res;"};
static const lean_object* l_Lean_IR_EmitC_emitInitFn___closed__6 = (const lean_object*)&l_Lean_IR_EmitC_emitInitFn___closed__6_value;
static const lean_string_object l_Lean_IR_EmitC_emitInitFn___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = ") return lean_io_result_mk_ok(lean_box(0));"};
static const lean_object* l_Lean_IR_EmitC_emitInitFn___closed__7 = (const lean_object*)&l_Lean_IR_EmitC_emitInitFn___closed__7_value;
static const lean_string_object l_Lean_IR_EmitC_emitInitFn___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " = true;"};
static const lean_object* l_Lean_IR_EmitC_emitInitFn___closed__8 = (const lean_object*)&l_Lean_IR_EmitC_emitInitFn___closed__8_value;
static const lean_string_object l_Lean_IR_EmitC_emitInitFn___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "return lean_io_result_mk_ok(lean_box(0));"};
static const lean_object* l_Lean_IR_EmitC_emitInitFn___closed__9 = (const lean_object*)&l_Lean_IR_EmitC_emitInitFn___closed__9_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitInitFn___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitInitFn___closed__9_value),((lean_object*)&l_Lean_IR_EmitC_emitMainFn___closed__35_value)}};
static const lean_object* l_Lean_IR_EmitC_emitInitFn___closed__10 = (const lean_object*)&l_Lean_IR_EmitC_emitInitFn___closed__10_value;
lean_object* l_Lean_mkModuleInitializationPrefix(uint8_t);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInitFn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInitFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_IR_EmitC_emitInitFn_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_IR_EmitC_emitInitFn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLegacyInitFn___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLegacyInitFn___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLegacyInitFn___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLegacyInitFn___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitLegacyInitFn_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitLegacyInitFn_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_IR_EmitC_emitLegacyInitFn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_IR_EmitC_emitLegacyInitFn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_EmitC_emitLegacyInitFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "static bool _G_initialized = false;"};
static const lean_object* l_Lean_IR_EmitC_emitLegacyInitFn___closed__0 = (const lean_object*)&l_Lean_IR_EmitC_emitLegacyInitFn___closed__0_value;
static const lean_string_object l_Lean_IR_EmitC_emitLegacyInitFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));"};
static const lean_object* l_Lean_IR_EmitC_emitLegacyInitFn___closed__1 = (const lean_object*)&l_Lean_IR_EmitC_emitLegacyInitFn___closed__1_value;
static const lean_string_object l_Lean_IR_EmitC_emitLegacyInitFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "_G_initialized = true;"};
static const lean_object* l_Lean_IR_EmitC_emitLegacyInitFn___closed__2 = (const lean_object*)&l_Lean_IR_EmitC_emitLegacyInitFn___closed__2_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitLegacyInitFn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitLegacyInitFn___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_IR_EmitC_emitLegacyInitFn___closed__3 = (const lean_object*)&l_Lean_IR_EmitC_emitLegacyInitFn___closed__3_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitLegacyInitFn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitLegacyInitFn___closed__1_value),((lean_object*)&l_Lean_IR_EmitC_emitLegacyInitFn___closed__3_value)}};
static const lean_object* l_Lean_IR_EmitC_emitLegacyInitFn___closed__4 = (const lean_object*)&l_Lean_IR_EmitC_emitLegacyInitFn___closed__4_value;
static const lean_ctor_object l_Lean_IR_EmitC_emitLegacyInitFn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_EmitC_emitInitFn___closed__6_value),((lean_object*)&l_Lean_IR_EmitC_emitLegacyInitFn___closed__4_value)}};
static const lean_object* l_Lean_IR_EmitC_emitLegacyInitFn___closed__5 = (const lean_object*)&l_Lean_IR_EmitC_emitLegacyInitFn___closed__5_value;
static const lean_closure_object l_Lean_IR_EmitC_emitLegacyInitFn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_EmitC_emitLegacyInitFn___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_EmitC_emitLegacyInitFn___closed__6 = (const lean_object*)&l_Lean_IR_EmitC_emitLegacyInitFn___closed__6_value;
static const lean_string_object l_Lean_IR_EmitC_emitLegacyInitFn___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "(builtin);"};
static const lean_object* l_Lean_IR_EmitC_emitLegacyInitFn___closed__7 = (const lean_object*)&l_Lean_IR_EmitC_emitLegacyInitFn___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLegacyInitFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitLegacyInitFn_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitLegacyInitFn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_main(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_IR_emitC___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_emitC___closed__0;
static lean_once_cell_t l_Lean_IR_emitC___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_emitC___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_emitC(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getEnv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getEnv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_getEnv(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getModName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getModName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_getModName(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getModInitFn(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_box(0);
x_10 = lean_box(0);
x_11 = l_Lean_PersistentEnvExtension_getState___redArg(x_9, x_6, x_4, x_8, x_10);
lean_dec(x_8);
x_12 = l_Lean_mkModuleInitializationFunctionName(x_5, x_11, x_1);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getModInitFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_IR_EmitC_getModInitFn(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = 0;
lean_inc(x_1);
x_6 = l_Lean_IR_findEnvDecl(x_4, x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = ((lean_object*)(l_Lean_IR_EmitC_getDecl___closed__0));
x_8 = 1;
x_9 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_8);
x_10 = lean_string_append(x_7, x_9);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l_Lean_IR_EmitC_getDecl___closed__1));
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec_ref(x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_apply_1(x_1, x_2);
x_6 = lean_string_append(x_3, x_5);
lean_dec_ref(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_3);
x_8 = lean_string_append(x_5, x_7);
lean_dec_ref(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emit(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_apply_1(x_1, x_2);
x_5 = lean_string_append(x_3, x_4);
lean_dec_ref(x_4);
x_6 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_7 = lean_box(0);
x_8 = lean_string_append(x_5, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_apply_1(x_2, x_3);
x_7 = lean_string_append(x_5, x_6);
lean_dec_ref(x_6);
x_8 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_9 = lean_box(0);
x_10 = lean_string_append(x_7, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitLn(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_apply_1(x_1, x_2);
x_6 = lean_string_append(x_4, x_5);
lean_dec_ref(x_5);
x_7 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_8 = lean_box(0);
x_9 = lean_string_append(x_6, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitLns___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitLns___redArg___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_IR_EmitC_emitLns___redArg___closed__9));
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitLns___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_obj_once(&l_Lean_IR_EmitC_emitLns___redArg___closed__10, &l_Lean_IR_EmitC_emitLns___redArg___closed__10_once, _init_l_Lean_IR_EmitC_emitLns___redArg___closed__10);
x_7 = l_List_forM___redArg(x_6, x_2, x_5);
x_8 = lean_apply_2(x_7, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitLns___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_argToCString(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
x_4 = l_Nat_reprFast(x_2);
x_5 = lean_string_append(x_3, x_4);
lean_dec_ref(x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__1));
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArg___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_IR_EmitC_argToCString(x_1);
x_4 = lean_box(0);
x_5 = lean_string_append(x_2, x_3);
lean_dec_ref(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitArg___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_EmitC_toCType_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_panic___at___00Lean_IR_EmitC_toCType_spec__0___closed__0));
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCType___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_IR_EmitC_toCType___closed__9));
x_2 = lean_unsigned_to_nat(25u);
x_3 = lean_unsigned_to_nat(84u);
x_4 = ((lean_object*)(l_Lean_IR_EmitC_toCType___closed__8));
x_5 = ((lean_object*)(l_Lean_IR_EmitC_toCType___closed__7));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCType___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_IR_EmitC_toCType___closed__9));
x_2 = lean_unsigned_to_nat(25u);
x_3 = lean_unsigned_to_nat(85u);
x_4 = ((lean_object*)(l_Lean_IR_EmitC_toCType___closed__8));
x_5 = ((lean_object*)(l_Lean_IR_EmitC_toCType___closed__7));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCType(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lean_IR_EmitC_toCType___closed__0));
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lean_IR_EmitC_toCType___closed__1));
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = ((lean_object*)(l_Lean_IR_EmitC_toCType___closed__2));
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = ((lean_object*)(l_Lean_IR_EmitC_toCType___closed__3));
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = ((lean_object*)(l_Lean_IR_EmitC_toCType___closed__4));
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = ((lean_object*)(l_Lean_IR_EmitC_toCType___closed__5));
return x_7;
}
case 9:
{
lean_object* x_8; 
x_8 = ((lean_object*)(l_Lean_IR_EmitC_toCType___closed__6));
return x_8;
}
case 10:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_obj_once(&l_Lean_IR_EmitC_toCType___closed__10, &l_Lean_IR_EmitC_toCType___closed__10_once, _init_l_Lean_IR_EmitC_toCType___closed__10);
x_10 = l_panic___at___00Lean_IR_EmitC_toCType_spec__0(x_9);
return x_10;
}
case 11:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_obj_once(&l_Lean_IR_EmitC_toCType___closed__11, &l_Lean_IR_EmitC_toCType___closed__11_once, _init_l_Lean_IR_EmitC_toCType___closed__11);
x_12 = l_panic___at___00Lean_IR_EmitC_toCType_spec__0(x_11);
return x_12;
}
default: 
{
lean_object* x_13; 
x_13 = ((lean_object*)(l_Lean_IR_EmitC_toCType___closed__12));
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_EmitC_toCType(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toHexDigit(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Nat_digitChar(x_1);
x_3 = ((lean_object*)(l_panic___at___00Lean_IR_EmitC_toCType_spec__0___closed__0));
x_4 = lean_string_push(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toHexDigit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_EmitC_toHexDigit(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_nat_sub(x_6, x_5);
x_8 = lean_nat_dec_eq(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_9 = lean_string_utf8_next_fast(x_2, x_3);
x_10 = lean_string_utf8_get_fast(x_2, x_3);
lean_dec(x_3);
x_11 = 10;
x_12 = lean_uint32_dec_eq(x_10, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 13;
x_14 = lean_uint32_dec_eq(x_10, x_13);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 9;
x_16 = lean_uint32_dec_eq(x_10, x_15);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 92;
x_18 = lean_uint32_dec_eq(x_10, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 34;
x_20 = lean_uint32_dec_eq(x_10, x_19);
if (x_20 == 0)
{
uint32_t x_21; uint8_t x_22; 
x_21 = 63;
x_22 = lean_uint32_dec_eq(x_10, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_uint32_to_nat(x_10);
x_24 = lean_unsigned_to_nat(31u);
x_25 = lean_nat_dec_le(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
x_26 = ((lean_object*)(l_panic___at___00Lean_IR_EmitC_toCType_spec__0___closed__0));
x_27 = lean_string_push(x_26, x_10);
x_28 = lean_string_append(x_4, x_27);
lean_dec_ref(x_27);
x_3 = x_9;
x_4 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__0));
x_31 = lean_unsigned_to_nat(16u);
x_32 = lean_unsigned_to_nat(4u);
x_33 = lean_nat_shiftr(x_23, x_32);
x_34 = l_Lean_IR_EmitC_toHexDigit(x_33);
lean_dec(x_33);
x_35 = lean_string_append(x_30, x_34);
lean_dec_ref(x_34);
x_36 = lean_nat_mod(x_23, x_31);
lean_dec(x_23);
x_37 = l_Lean_IR_EmitC_toHexDigit(x_36);
lean_dec(x_36);
x_38 = lean_string_append(x_35, x_37);
lean_dec_ref(x_37);
x_39 = lean_string_append(x_4, x_38);
lean_dec_ref(x_38);
x_3 = x_9;
x_4 = x_39;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__1));
x_42 = lean_string_append(x_4, x_41);
x_3 = x_9;
x_4 = x_42;
goto _start;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__2));
x_45 = lean_string_append(x_4, x_44);
x_3 = x_9;
x_4 = x_45;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__3));
x_48 = lean_string_append(x_4, x_47);
x_3 = x_9;
x_4 = x_48;
goto _start;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__4));
x_51 = lean_string_append(x_4, x_50);
x_3 = x_9;
x_4 = x_51;
goto _start;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__5));
x_54 = lean_string_append(x_4, x_53);
x_3 = x_9;
x_4 = x_54;
goto _start;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___closed__6));
x_57 = lean_string_append(x_4, x_56);
x_3 = x_9;
x_4 = x_57;
goto _start;
}
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_quoteString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = ((lean_object*)(l_Lean_IR_EmitC_quoteString___closed__0));
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_positions(x_5);
x_7 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg(x_5, x_1, x_6, x_2);
lean_dec_ref(x_1);
lean_dec_ref(x_5);
x_8 = lean_string_append(x_7, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_EmitC_quoteString_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwInvalidExportName___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = ((lean_object*)(l_Lean_IR_EmitC_throwInvalidExportName___redArg___closed__0));
x_4 = 1;
x_5 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_4);
x_6 = lean_string_append(x_3, x_5);
lean_dec_ref(x_5);
x_7 = ((lean_object*)(l_Lean_IR_EmitC_getDecl___closed__1));
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwInvalidExportName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_throwInvalidExportName___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwInvalidExportName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_throwInvalidExportName(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_1);
lean_inc_ref(x_4);
x_5 = lean_get_export_name_for(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = ((lean_object*)(l_Lean_IR_EmitC_toCName___closed__1));
x_7 = lean_name_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_get_symbol_stem(x_4, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_4);
lean_dec(x_1);
x_10 = ((lean_object*)(l_Lean_IR_EmitC_leanMainFn___closed__0));
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
else
{
lean_object* x_12; 
lean_dec_ref(x_4);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec_ref(x_5);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec_ref(x_12);
x_16 = l_Lean_IR_EmitC_throwInvalidExportName___redArg(x_1, x_3);
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec(x_12);
x_17 = l_Lean_IR_EmitC_throwInvalidExportName___redArg(x_1, x_3);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_toCName(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_15; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
x_7 = x_4;
x_8 = x_15;
goto block_14;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = lean_string_append(x_6, x_5);
lean_dec(x_5);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_10);
lean_ctor_set(x_7, 0, x_9);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_24 = !lean_is_exclusive(x_4);
if (x_24 == 0)
{
x_18 = x_4;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_17);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCInitName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_1);
lean_inc_ref(x_4);
x_5 = lean_get_export_name_for(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = ((lean_object*)(l_Lean_IR_EmitC_toCInitName___closed__0));
x_7 = lean_get_symbol_stem(x_4, x_1);
x_8 = lean_string_append(x_6, x_7);
lean_dec_ref(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec_ref(x_4);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec_ref(x_5);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_10);
x_13 = ((lean_object*)(l_Lean_IR_EmitC_toCInitName___closed__0));
x_14 = lean_string_append(x_13, x_12);
lean_dec_ref(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec_ref(x_10);
x_16 = l_Lean_IR_EmitC_throwInvalidExportName___redArg(x_1, x_3);
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec(x_10);
x_17 = l_Lean_IR_EmitC_throwInvalidExportName___redArg(x_1, x_3);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCInitName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_toCInitName(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_15; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
x_7 = x_4;
x_8 = x_15;
goto block_14;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = lean_string_append(x_6, x_5);
lean_dec(x_5);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_10);
lean_ctor_set(x_7, 0, x_9);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_24 = !lean_is_exclusive(x_4);
if (x_24 == 0)
{
x_18 = x_4;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_17);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_ctorScalarSizeStr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = ((lean_object*)(l_Lean_IR_EmitC_ctorScalarSizeStr___closed__0));
x_7 = l_Nat_reprFast(x_1);
x_8 = lean_string_append(x_6, x_7);
lean_dec_ref(x_7);
x_9 = ((lean_object*)(l_Lean_IR_EmitC_ctorScalarSizeStr___closed__1));
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Nat_reprFast(x_2);
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_13 = ((lean_object*)(l_Lean_IR_EmitC_ctorScalarSizeStr___closed__0));
x_14 = l_Nat_reprFast(x_1);
x_15 = lean_string_append(x_13, x_14);
lean_dec_ref(x_14);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = l_Nat_reprFast(x_2);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueName___closed__0));
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_findValueDecl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_11);
x_12 = l_Lean_Compiler_LCNF_getSimpleGroundExpr(x_11, x_1);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_1 = x_14;
goto _start;
}
else
{
lean_dec(x_13);
lean_dec_ref(x_3);
x_5 = x_1;
x_6 = x_2;
x_7 = x_4;
goto block_10;
}
}
else
{
lean_dec(x_12);
lean_dec_ref(x_3);
x_5 = x_1;
x_6 = x_2;
x_7 = x_4;
goto block_10;
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_findValueDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc_ref(x_3);
x_5 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_findValueDecl_spec__0(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_36; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_36 = !lean_is_exclusive(x_6);
if (x_36 == 0)
{
x_10 = x_6;
x_11 = x_36;
goto block_35;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_box(0);
x_11 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_12; 
x_12 = l_Lean_IR_EmitC_toCName(x_8, x_3, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_25; 
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_ctor_get(x_12, 1);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
x_15 = x_12;
x_16 = x_25;
goto block_24;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_17; lean_object* x_18; 
x_17 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueName(x_13);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_17);
x_18 = x_10;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_9);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_14);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
lean_del_object(x_10);
lean_dec(x_9);
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
x_28 = x_12;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
lean_dec_ref(x_3);
x_37 = lean_ctor_get(x_5, 0);
x_38 = lean_ctor_get(x_5, 1);
x_45 = !lean_is_exclusive(x_5);
if (x_45 == 0)
{
x_39 = x_5;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_5);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxValueName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueName(x_1);
x_4 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxValueName___closed__0));
x_5 = l_Nat_reprFast(x_2);
x_6 = lean_string_append(x_4, x_5);
lean_dec_ref(x_5);
x_7 = lean_string_append(x_3, x_6);
lean_dec_ref(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_4, x_6);
x_8 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxValueName(x_1, x_4);
x_9 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__0));
x_10 = lean_string_append(x_9, x_2);
x_11 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__1));
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_string_append(x_12, x_8);
x_14 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__2));
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_3);
x_17 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__3));
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_5, x_18);
lean_dec_ref(x_18);
x_20 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_7);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__0));
x_7 = l_Nat_reprFast(x_5);
x_8 = lean_string_append(x_6, x_7);
lean_dec_ref(x_7);
x_9 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__1));
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec_ref(x_1);
x_14 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_findValueDecl(x_13, x_2, x_3, x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_36; 
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_ctor_get(x_14, 1);
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
x_17 = x_14;
x_18 = x_36;
goto block_35;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_34; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
x_21 = x_15;
x_22 = x_34;
goto block_33;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_box(0);
x_22 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__2));
x_24 = lean_string_append(x_23, x_19);
lean_dec(x_19);
x_25 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__3));
x_26 = lean_string_append(x_24, x_25);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_26);
x_27 = x_21;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_20);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_27);
x_28 = x_17;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_16);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
else
{
return x_14;
}
}
default: 
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_3);
x_37 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_37);
lean_dec_ref(x_1);
x_38 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__2));
x_39 = lean_string_append(x_38, x_37);
lean_dec_ref(x_37);
x_40 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__3));
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_2);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_4);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__0));
x_6 = lean_apply_1(x_1, x_2);
x_7 = lean_string_append(x_5, x_6);
lean_dec_ref(x_6);
x_8 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__1));
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Nat_reprFast(x_3);
x_11 = lean_string_append(x_9, x_10);
lean_dec_ref(x_10);
x_12 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__2));
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Nat_reprFast(x_4);
x_15 = lean_string_append(x_13, x_14);
lean_dec_ref(x_14);
x_16 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__3));
x_17 = lean_string_append(x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkCtorHeader_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__0));
x_5 = lean_string_append(x_4, x_1);
x_6 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__1));
x_7 = lean_string_append(x_5, x_6);
x_8 = l_Nat_reprFast(x_2);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__2));
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Nat_reprFast(x_3);
x_13 = lean_string_append(x_11, x_12);
lean_dec_ref(x_12);
x_14 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__3));
x_15 = lean_string_append(x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkCtorHeader_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkCtorHeader_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkCtorHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkCtorHeader___closed__0));
lean_inc(x_1);
x_6 = l_Nat_reprFast(x_1);
x_7 = lean_string_append(x_5, x_6);
lean_dec_ref(x_6);
x_8 = ((lean_object*)(l_Lean_IR_EmitC_ctorScalarSizeStr___closed__1));
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Lean_IR_EmitC_ctorScalarSizeStr(x_2, x_3);
x_11 = lean_string_append(x_9, x_10);
lean_dec_ref(x_10);
x_12 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkCtorHeader_spec__0(x_11, x_1, x_4);
lean_dec_ref(x_11);
return x_12;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_IR_EmitC_emitLns___redArg___closed__10, &l_Lean_IR_EmitC_emitLns___redArg___closed__10_once, _init_l_Lean_IR_EmitC_emitLns___redArg___closed__10);
x_2 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_IR_EmitC_emitLns___redArg___closed__10, &l_Lean_IR_EmitC_emitLns___redArg___closed__10_once, _init_l_Lean_IR_EmitC_emitLns___redArg___closed__10);
x_2 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_IR_EmitC_emitLns___redArg___closed__10, &l_Lean_IR_EmitC_emitLns___redArg___closed__10_once, _init_l_Lean_IR_EmitC_emitLns___redArg___closed__10);
x_2 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_IR_EmitC_emitLns___redArg___closed__10, &l_Lean_IR_EmitC_emitLns___redArg___closed__10_once, _init_l_Lean_IR_EmitC_emitLns___redArg___closed__10);
x_2 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_IR_EmitC_emitLns___redArg___closed__10, &l_Lean_IR_EmitC_emitLns___redArg___closed__10_once, _init_l_Lean_IR_EmitC_emitLns___redArg___closed__10);
x_2 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_IR_EmitC_emitLns___redArg___closed__10, &l_Lean_IR_EmitC_emitLns___redArg___closed__10_once, _init_l_Lean_IR_EmitC_emitLns___redArg___closed__10);
x_2 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_IR_EmitC_emitLns___redArg___closed__10, &l_Lean_IR_EmitC_emitLns___redArg___closed__10_once, _init_l_Lean_IR_EmitC_emitLns___redArg___closed__10);
x_2 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_5 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__0, &l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__0);
x_6 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__1, &l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__1_once, _init_l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__1);
x_7 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__2, &l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__2_once, _init_l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__2);
x_8 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__3, &l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__3_once, _init_l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__3);
x_9 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__4, &l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__4_once, _init_l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__5, &l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__5_once, _init_l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__5);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set(x_12, 3, x_7);
lean_ctor_set(x_12, 4, x_8);
x_13 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__6, &l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__6_once, _init_l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1___closed__6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = ((lean_object*)(l_panic___at___00Lean_IR_EmitC_toCType_spec__0___closed__0));
x_16 = l_instInhabitedOfMonad___redArg(x_14, x_15);
x_17 = lean_panic_fn(x_16, x_1);
x_18 = lean_apply_3(x_17, x_2, x_3, x_4);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget_borrowed(x_3, x_2);
lean_inc_ref(x_5);
lean_inc(x_10);
x_11 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit(x_10, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_17, x_2, x_14);
x_2 = x_19;
x_3 = x_20;
x_4 = x_15;
x_6 = x_13;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
x_24 = x_11;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__0(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__2___closed__0));
x_9 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_10 = lean_uint64_to_nat(x_9);
x_11 = l_Nat_reprFast(x_10);
x_12 = lean_string_append(x_8, x_11);
lean_dec_ref(x_11);
x_13 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__2___closed__1));
x_14 = lean_string_append(x_12, x_13);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_7, x_2, x_14);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_1);
if (x_5 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_6 = lean_unsigned_to_nat(8u);
x_7 = l_instInhabitedUInt8;
x_8 = lean_nat_mul(x_3, x_6);
x_9 = lean_box(x_7);
x_10 = lean_array_get_borrowed(x_9, x_2, x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_8, x_11);
x_13 = lean_box(x_7);
x_14 = lean_array_get_borrowed(x_13, x_2, x_12);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_add(x_8, x_15);
x_17 = lean_box(x_7);
x_18 = lean_array_get_borrowed(x_17, x_2, x_16);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(3u);
x_20 = lean_nat_add(x_8, x_19);
x_21 = lean_box(x_7);
x_22 = lean_array_get_borrowed(x_21, x_2, x_20);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(4u);
x_24 = lean_nat_add(x_8, x_23);
x_25 = lean_box(x_7);
x_26 = lean_array_get_borrowed(x_25, x_2, x_24);
lean_dec(x_24);
x_27 = lean_unsigned_to_nat(5u);
x_28 = lean_nat_add(x_8, x_27);
x_29 = lean_box(x_7);
x_30 = lean_array_get_borrowed(x_29, x_2, x_28);
lean_dec(x_28);
x_31 = lean_unsigned_to_nat(6u);
x_32 = lean_nat_add(x_8, x_31);
x_33 = lean_box(x_7);
x_34 = lean_array_get_borrowed(x_33, x_2, x_32);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(7u);
x_36 = lean_nat_add(x_8, x_35);
lean_dec(x_8);
x_37 = lean_box(x_7);
x_38 = lean_array_get_borrowed(x_37, x_2, x_36);
lean_dec(x_36);
x_39 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__0));
x_40 = lean_unbox(x_10);
x_41 = lean_uint8_to_nat(x_40);
x_42 = l_Nat_reprFast(x_41);
x_43 = lean_string_append(x_39, x_42);
lean_dec_ref(x_42);
x_44 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_unbox(x_14);
x_47 = lean_uint8_to_nat(x_46);
x_48 = l_Nat_reprFast(x_47);
x_49 = lean_string_append(x_45, x_48);
lean_dec_ref(x_48);
x_50 = lean_string_append(x_49, x_44);
x_51 = lean_unbox(x_18);
x_52 = lean_uint8_to_nat(x_51);
x_53 = l_Nat_reprFast(x_52);
x_54 = lean_string_append(x_50, x_53);
lean_dec_ref(x_53);
x_55 = lean_string_append(x_54, x_44);
x_56 = lean_unbox(x_22);
x_57 = lean_uint8_to_nat(x_56);
x_58 = l_Nat_reprFast(x_57);
x_59 = lean_string_append(x_55, x_58);
lean_dec_ref(x_58);
x_60 = lean_string_append(x_59, x_44);
x_61 = lean_unbox(x_26);
x_62 = lean_uint8_to_nat(x_61);
x_63 = l_Nat_reprFast(x_62);
x_64 = lean_string_append(x_60, x_63);
lean_dec_ref(x_63);
x_65 = lean_string_append(x_64, x_44);
x_66 = lean_unbox(x_30);
x_67 = lean_uint8_to_nat(x_66);
x_68 = l_Nat_reprFast(x_67);
x_69 = lean_string_append(x_65, x_68);
lean_dec_ref(x_68);
x_70 = lean_string_append(x_69, x_44);
x_71 = lean_unbox(x_34);
x_72 = lean_uint8_to_nat(x_71);
x_73 = l_Nat_reprFast(x_72);
x_74 = lean_string_append(x_70, x_73);
lean_dec_ref(x_73);
x_75 = lean_string_append(x_74, x_44);
x_76 = lean_unbox(x_38);
x_77 = lean_uint8_to_nat(x_76);
x_78 = l_Nat_reprFast(x_77);
x_79 = lean_string_append(x_75, x_78);
lean_dec_ref(x_78);
x_80 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__3));
x_81 = lean_string_append(x_79, x_80);
x_82 = lean_array_push(x_4, x_81);
x_83 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_83;
x_4 = x_82;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__1));
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_unsigned_to_nat(249u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__0));
x_5 = ((lean_object*)(l_Lean_IR_EmitC_toCType___closed__7));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_array_size(x_2);
x_10 = 0;
lean_inc_ref(x_6);
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__0(x_9, x_10, x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_56; 
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_11, 1);
x_56 = !lean_is_exclusive(x_11);
if (x_56 == 0)
{
x_14 = x_11;
x_15 = x_56;
goto block_55;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_54; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
x_54 = !lean_is_exclusive(x_12);
if (x_54 == 0)
{
x_18 = x_12;
x_19 = x_54;
goto block_53;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_array_get_size(x_4);
x_21 = lean_unsigned_to_nat(8u);
x_22 = lean_nat_mod(x_20, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_del_object(x_18);
lean_dec(x_16);
lean_del_object(x_14);
lean_dec_ref(x_3);
lean_dec(x_1);
x_25 = lean_obj_once(&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__2, &l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__2_once, _init_l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__2);
x_26 = l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1(x_25, x_17, x_6, x_13);
return x_26;
}
else
{
lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_6);
x_27 = lean_array_get_size(x_3);
x_28 = lean_array_size(x_3);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_shiftr(x_20, x_29);
x_31 = lean_mk_empty_array_with_capacity(x_30);
x_32 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkCtorHeader(x_8, x_27, x_20, x_1);
x_33 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__2(x_28, x_10, x_3);
x_34 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg(x_30, x_4, x_23, x_31);
lean_dec(x_30);
x_35 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__3));
x_36 = l_Array_append___redArg(x_16, x_33);
lean_dec_ref(x_33);
x_37 = l_Array_append___redArg(x_36, x_34);
lean_dec_ref(x_34);
x_38 = lean_array_to_list(x_37);
x_39 = l_String_intercalate(x_35, x_38);
x_40 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__4));
x_41 = lean_string_append(x_40, x_32);
lean_dec_ref(x_32);
x_42 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__5));
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_string_append(x_43, x_39);
lean_dec_ref(x_39);
x_45 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__6));
x_46 = lean_string_append(x_44, x_45);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_46);
x_47 = x_18;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_17);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_47);
x_48 = x_14;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_13);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_65; 
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec(x_1);
x_57 = lean_ctor_get(x_11, 0);
x_58 = lean_ctor_get(x_11, 1);
x_65 = !lean_is_exclusive(x_11);
if (x_65 == 0)
{
x_59 = x_11;
x_60 = x_65;
goto block_64;
}
else
{
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_11);
x_59 = lean_box(0);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
if (x_60 == 0)
{
x_61 = x_59;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_58);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg(x_1, x_2, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__1));
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_unsigned_to_nat(216u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__0));
x_5 = ((lean_object*)(l_Lean_IR_EmitC_toCType___closed__7));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__3___boxed__const__1(void) {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_instInhabitedUInt64;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__3___boxed__const__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__6));
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_array_push(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_9 = lean_obj_once(&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__2, &l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__2_once, _init_l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__2);
x_10 = l_panic___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__1(x_9, x_3, x_4, x_5);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_dec_eq(x_7, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_obj_once(&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__3, &l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__3_once, _init_l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__3);
x_14 = l_Array_back_x21___redArg(x_13, x_2);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_pop(x_2);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_18 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit(x_1, x_17, x_3, x_4, x_5);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__4));
x_24 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg(x_1, x_23, x_21, x_22, x_20);
lean_dec(x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_unbox_uint64(x_16);
lean_dec(x_16);
x_30 = l_Lean_Compiler_LCNF_uint64ToByteArrayLE(x_29);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_27);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_15);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_mk_empty_array_with_capacity(x_33);
x_35 = lean_array_push(x_34, x_31);
x_36 = lean_array_push(x_35, x_32);
x_37 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__5));
x_38 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor(x_11, x_36, x_37, x_30, x_28, x_4, x_26);
lean_dec_ref(x_30);
return x_38;
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_4);
return x_24;
}
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_18;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint64_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_1);
x_39 = lean_obj_once(&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__3, &l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__3_once, _init_l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__3);
x_40 = lean_array_get(x_39, x_2, x_6);
lean_dec_ref(x_2);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_unbox_uint64(x_42);
lean_dec(x_42);
x_44 = l_Lean_Compiler_LCNF_uint64ToByteArrayLE(x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_41);
x_46 = lean_obj_once(&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__7, &l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__7_once, _init_l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__7);
x_47 = lean_array_push(x_46, x_45);
x_48 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__5));
x_49 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor(x_11, x_47, x_48, x_44, x_3, x_4, x_5);
lean_dec_ref(x_44);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueCLit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueName(x_1);
x_7 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__0));
x_8 = lean_string_append(x_7, x_2);
x_9 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__1));
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_6);
x_12 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__2));
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_string_append(x_13, x_3);
x_15 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__3));
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_5, x_16);
lean_dec_ref(x_16);
x_18 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueCLit___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueCLit___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueCLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueCLit___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueCLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueCLit(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_4 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__0));
x_5 = l_Nat_reprFast(x_1);
x_6 = lean_string_append(x_4, x_5);
lean_dec_ref(x_5);
x_7 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__1));
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Nat_reprFast(x_2);
x_10 = lean_string_append(x_8, x_9);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__2));
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Nat_reprFast(x_3);
x_14 = lean_string_append(x_12, x_13);
lean_dec_ref(x_13);
x_15 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__3));
x_16 = lean_string_append(x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = lean_uint8_to_nat(x_8);
x_10 = l_Nat_reprFast(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_7, x_2, x_10);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue_spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(249u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue_spec__0(x_2, x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__0, &l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__0_once, _init_l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__0);
x_2 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__4));
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__3));
x_2 = lean_obj_once(&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__2, &l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__2_once, _init_l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__2);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
x_10 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor(x_6, x_7, x_8, x_9, x_3, x_4, x_5);
lean_dec_ref(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__4));
x_16 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueCLit___redArg(x_1, x_15, x_13, x_14, x_12);
lean_dec(x_13);
return x_16;
}
else
{
lean_dec_ref(x_1);
return x_10;
}
}
case 1:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_4);
x_17 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_2);
x_18 = lean_string_utf8_byte_size(x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_18, x_19);
x_21 = lean_string_length(x_17);
x_22 = l_Lean_IR_EmitC_quoteString(x_17);
x_23 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__1));
x_24 = lean_obj_once(&l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__4, &l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__4_once, _init_l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__4);
x_25 = l_Nat_reprFast(x_20);
x_26 = lean_string_append(x_24, x_25);
x_27 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__5));
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_string_append(x_28, x_25);
lean_dec_ref(x_25);
x_30 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__6));
x_31 = lean_string_append(x_29, x_30);
x_32 = l_Nat_reprFast(x_21);
x_33 = lean_string_append(x_31, x_32);
lean_dec_ref(x_32);
x_34 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__7));
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_string_append(x_35, x_22);
lean_dec_ref(x_22);
x_37 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__3));
x_38 = lean_string_append(x_36, x_37);
x_39 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueCLit___redArg(x_1, x_23, x_38, x_3, x_5);
lean_dec_ref(x_38);
return x_39;
}
case 2:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_41);
lean_dec_ref(x_2);
lean_inc_ref(x_4);
lean_inc(x_40);
x_42 = l_Lean_IR_EmitC_toCName(x_40, x_4, x_5);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
lean_inc_ref(x_4);
x_45 = l_Lean_IR_EmitC_getDecl(x_40, x_4, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = lean_array_get_size(x_41);
x_49 = lean_array_size(x_41);
x_50 = 0;
x_51 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__0(x_49, x_50, x_41, x_3, x_4, x_47);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_unsigned_to_nat(245u);
x_57 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__8));
x_58 = l_Nat_reprFast(x_48);
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_unsigned_to_nat(0u);
x_61 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkCtorHeader_spec__0(x_59, x_60, x_56);
lean_dec_ref(x_59);
x_62 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__9));
x_63 = lean_string_append(x_62, x_43);
lean_dec(x_43);
x_64 = l_Lean_IR_Decl_params(x_46);
lean_dec(x_46);
x_65 = lean_array_get_size(x_64);
lean_dec_ref(x_64);
x_66 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__3));
x_67 = lean_array_to_list(x_54);
x_68 = l_String_intercalate(x_66, x_67);
x_69 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__10));
x_70 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__4));
x_71 = lean_string_append(x_70, x_61);
lean_dec_ref(x_61);
x_72 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__11));
x_73 = lean_string_append(x_71, x_72);
x_74 = lean_string_append(x_73, x_63);
lean_dec_ref(x_63);
x_75 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__12));
x_76 = lean_string_append(x_74, x_75);
x_77 = l_Nat_reprFast(x_65);
x_78 = lean_string_append(x_76, x_77);
lean_dec_ref(x_77);
x_79 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__13));
x_80 = lean_string_append(x_78, x_79);
x_81 = lean_string_append(x_80, x_58);
lean_dec_ref(x_58);
x_82 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__5));
x_83 = lean_string_append(x_81, x_82);
x_84 = lean_string_append(x_83, x_68);
lean_dec_ref(x_68);
x_85 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__14));
x_86 = lean_string_append(x_84, x_85);
x_87 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueCLit___redArg(x_1, x_69, x_86, x_55, x_53);
lean_dec_ref(x_86);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_96; 
lean_dec(x_46);
lean_dec(x_43);
lean_dec_ref(x_1);
x_88 = lean_ctor_get(x_51, 0);
x_89 = lean_ctor_get(x_51, 1);
x_96 = !lean_is_exclusive(x_51);
if (x_96 == 0)
{
x_90 = x_51;
x_91 = x_96;
goto block_95;
}
else
{
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_51);
x_90 = lean_box(0);
x_91 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_92; 
if (x_91 == 0)
{
x_92 = x_90;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_88);
lean_ctor_set(x_94, 1, x_89);
x_92 = x_94;
goto block_93;
}
block_93:
{
return x_92;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_105; 
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_97 = lean_ctor_get(x_45, 0);
x_98 = lean_ctor_get(x_45, 1);
x_105 = !lean_is_exclusive(x_45);
if (x_105 == 0)
{
x_99 = x_45;
x_100 = x_105;
goto block_104;
}
else
{
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_45);
x_99 = lean_box(0);
x_100 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_101; 
if (x_100 == 0)
{
x_101 = x_99;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_97);
lean_ctor_set(x_103, 1, x_98);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
}
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_114; 
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_106 = lean_ctor_get(x_42, 0);
x_107 = lean_ctor_get(x_42, 1);
x_114 = !lean_is_exclusive(x_42);
if (x_114 == 0)
{
x_108 = x_42;
x_109 = x_114;
goto block_113;
}
else
{
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_42);
x_108 = lean_box(0);
x_109 = x_114;
goto block_113;
}
block_113:
{
lean_object* x_110; 
if (x_109 == 0)
{
x_110 = x_108;
goto block_111;
}
else
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_106);
lean_ctor_set(x_112, 1, x_107);
x_110 = x_112;
goto block_111;
}
block_111:
{
return x_110;
}
}
}
}
case 3:
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_115);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_116 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit(x_1, x_115, x_3, x_4, x_5);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec_ref(x_116);
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
x_121 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__4));
x_122 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueCLit___redArg(x_1, x_121, x_119, x_120, x_118);
lean_dec(x_119);
return x_122;
}
else
{
lean_dec_ref(x_1);
return x_116;
}
}
case 4:
{
lean_object* x_123; lean_object* x_124; 
lean_dec_ref(x_1);
x_123 = lean_ctor_get(x_2, 0);
lean_inc(x_123);
lean_dec_ref(x_2);
x_124 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_findValueDecl(x_123, x_3, x_4, x_5);
return x_124;
}
case 5:
{
lean_object* x_125; lean_object* x_126; size_t x_127; size_t x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_125);
lean_dec_ref(x_2);
x_126 = lean_array_get_size(x_125);
x_127 = lean_array_size(x_125);
x_128 = 0;
x_129 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__0(x_127, x_128, x_125, x_3, x_4, x_5);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec_ref(x_129);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_unsigned_to_nat(246u);
x_135 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__15));
x_136 = l_Nat_reprFast(x_126);
x_137 = lean_string_append(x_135, x_136);
x_138 = lean_unsigned_to_nat(0u);
x_139 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkCtorHeader_spec__0(x_137, x_138, x_134);
lean_dec_ref(x_137);
x_140 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__3));
x_141 = lean_array_to_list(x_132);
x_142 = l_String_intercalate(x_140, x_141);
x_143 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__16));
x_144 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__4));
x_145 = lean_string_append(x_144, x_139);
lean_dec_ref(x_139);
x_146 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__3));
x_147 = lean_string_append(x_145, x_146);
x_148 = lean_string_append(x_147, x_136);
x_149 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__5));
x_150 = lean_string_append(x_148, x_149);
x_151 = lean_string_append(x_150, x_136);
lean_dec_ref(x_136);
x_152 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__17));
x_153 = lean_string_append(x_151, x_152);
x_154 = lean_string_append(x_153, x_142);
lean_dec_ref(x_142);
x_155 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__6));
x_156 = lean_string_append(x_154, x_155);
x_157 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueCLit___redArg(x_1, x_143, x_156, x_133, x_131);
lean_dec_ref(x_156);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_166; 
lean_dec_ref(x_1);
x_158 = lean_ctor_get(x_129, 0);
x_159 = lean_ctor_get(x_129, 1);
x_166 = !lean_is_exclusive(x_129);
if (x_166 == 0)
{
x_160 = x_129;
x_161 = x_166;
goto block_165;
}
else
{
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_129);
x_160 = lean_box(0);
x_161 = x_166;
goto block_165;
}
block_165:
{
lean_object* x_162; 
if (x_161 == 0)
{
x_162 = x_160;
goto block_163;
}
else
{
lean_object* x_164; 
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_159);
x_162 = x_164;
goto block_163;
}
block_163:
{
return x_162;
}
}
}
}
default: 
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; size_t x_175; size_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec_ref(x_4);
x_167 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_167);
lean_dec_ref(x_2);
x_168 = lean_unsigned_to_nat(248u);
x_169 = lean_unsigned_to_nat(1u);
x_170 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__18));
x_171 = lean_array_get_size(x_167);
x_172 = l_Nat_reprFast(x_171);
x_173 = lean_string_append(x_170, x_172);
x_174 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkCtorHeader_spec__0(x_173, x_169, x_168);
lean_dec_ref(x_173);
x_175 = lean_array_size(x_167);
x_176 = 0;
x_177 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue_spec__1(x_175, x_176, x_167);
x_178 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__3));
x_179 = lean_array_to_list(x_177);
x_180 = l_String_intercalate(x_178, x_179);
x_181 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__19));
x_182 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__4));
x_183 = lean_string_append(x_182, x_174);
lean_dec_ref(x_174);
x_184 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__3));
x_185 = lean_string_append(x_183, x_184);
x_186 = lean_string_append(x_185, x_172);
x_187 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__5));
x_188 = lean_string_append(x_186, x_187);
x_189 = lean_string_append(x_188, x_172);
lean_dec_ref(x_172);
x_190 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue___closed__17));
x_191 = lean_string_append(x_189, x_190);
x_192 = lean_string_append(x_191, x_180);
lean_dec_ref(x_180);
x_193 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor___closed__6));
x_194 = lean_string_append(x_192, x_193);
x_195 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkValueCLit___redArg(x_1, x_181, x_194, x_3, x_5);
lean_dec_ref(x_194);
return x_195;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGround(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc_ref(x_5);
lean_inc_ref(x_2);
x_7 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGroundToValue(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_44; 
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_44 = !lean_is_exclusive(x_7);
if (x_44 == 0)
{
x_10 = x_7;
x_11 = x_44;
goto block_43;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_42; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
x_14 = x_8;
x_15 = x_42;
goto block_41;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_box(0);
x_15 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_16; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_36);
lean_dec_ref(x_5);
x_37 = l_Lean_IR_Decl_name(x_1);
x_38 = l_Lean_isClosedTermName(x_36, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGround___closed__2));
x_16 = x_39;
goto block_35;
}
else
{
lean_object* x_40; 
x_40 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGround___closed__3));
x_16 = x_40;
goto block_35;
}
block_35:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGround___closed__0));
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_2);
lean_dec_ref(x_2);
x_20 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGround___closed__1));
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_string_append(x_21, x_12);
lean_dec(x_12);
x_23 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__3));
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_9, x_24);
lean_dec_ref(x_24);
x_26 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_27 = lean_box(0);
x_28 = lean_string_append(x_25, x_26);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_27);
x_29 = x_14;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_13);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_28);
lean_ctor_set(x_10, 0, x_29);
x_30 = x_10;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_28);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_53; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_45 = lean_ctor_get(x_7, 0);
x_46 = lean_ctor_get(x_7, 1);
x_53 = !lean_is_exclusive(x_7);
if (x_53 == 0)
{
x_47 = x_7;
x_48 = x_53;
goto block_52;
}
else
{
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_7);
x_47 = lean_box(0);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_48 == 0)
{
x_49 = x_47;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_46);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGround___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGround(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_EmitC_emitGroundDecl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = ((lean_object*)(l_panic___at___00Lean_IR_EmitC_toCType_spec__0___closed__0));
x_5 = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_panic_fn(x_6, x_1);
x_8 = lean_apply_2(x_7, x_2, x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitGroundDecl___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_IR_EmitC_emitGroundDecl___closed__1));
x_2 = lean_unsigned_to_nat(64u);
x_3 = lean_unsigned_to_nat(143u);
x_4 = ((lean_object*)(l_Lean_IR_EmitC_emitGroundDecl___closed__0));
x_5 = ((lean_object*)(l_Lean_IR_EmitC_toCType___closed__7));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitGroundDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_IR_Decl_name(x_1);
lean_inc_ref(x_5);
x_7 = l_Lean_Compiler_LCNF_getSimpleGroundExpr(x_5, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileGround(x_1, x_2, x_8, x_9, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
x_11 = lean_ctor_get(x_10, 1);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_10, 0);
lean_dec(x_20);
x_12 = x_10;
x_13 = x_19;
goto block_18;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_15 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_11);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
x_23 = x_10;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_7);
lean_dec_ref(x_2);
x_30 = lean_obj_once(&l_Lean_IR_EmitC_emitGroundDecl___closed__2, &l_Lean_IR_EmitC_emitGroundDecl___closed__2_once, _init_l_Lean_IR_EmitC_emitGroundDecl___closed__2);
x_31 = l_panic___at___00Lean_IR_EmitC_emitGroundDecl_spec__0(x_30, x_3, x_4);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitGroundDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitGroundDecl(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toTokenName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_IR_EmitC_toTokenName___closed__0));
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnClosedDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_4 = ((lean_object*)(l_Lean_IR_EmitC_emitFnClosedDecl___redArg___closed__0));
lean_inc_ref(x_2);
x_5 = l_Lean_IR_EmitC_toTokenName(x_2);
x_6 = lean_string_append(x_4, x_5);
lean_dec_ref(x_5);
x_7 = ((lean_object*)(l_Lean_IR_EmitC_emitFnClosedDecl___redArg___closed__1));
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_string_append(x_3, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_11 = lean_string_append(x_9, x_10);
x_12 = ((lean_object*)(l_Lean_IR_EmitC_emitFnClosedDecl___redArg___closed__2));
x_13 = l_Lean_IR_Decl_resultType(x_1);
x_14 = l_Lean_IR_EmitC_toCType(x_13);
lean_dec(x_13);
x_15 = lean_string_append(x_12, x_14);
lean_dec_ref(x_14);
x_16 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__1));
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_2);
lean_dec_ref(x_2);
x_19 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__3));
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_string_append(x_11, x_20);
lean_dec_ref(x_20);
x_22 = lean_box(0);
x_23 = lean_string_append(x_21, x_10);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnClosedDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitFnClosedDecl___redArg(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnClosedDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitFnClosedDecl___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnClosedDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitFnClosedDecl(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = lean_ctor_get(x_11, 1);
x_13 = l_Lean_IR_IRType_isErased(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_inc(x_11);
x_14 = lean_array_push(x_4, x_11);
x_5 = x_14;
goto block_9;
}
else
{
x_5 = x_4;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = lean_ctor_get(x_11, 1);
x_13 = l_Lean_IR_IRType_isVoid(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_inc(x_11);
x_14 = lean_array_push(x_4, x_11);
x_5 = x_14;
goto block_9;
}
else
{
x_5 = x_4;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__2(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitFnDeclAux_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 1)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_20; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_3);
x_11 = lean_nat_sub(x_2, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_20 = lean_nat_dec_lt(x_5, x_12);
if (x_20 == 0)
{
x_13 = x_4;
goto block_19;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_22 = lean_string_append(x_4, x_21);
x_13 = x_22;
goto block_19;
}
block_19:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_fget_borrowed(x_1, x_12);
lean_dec(x_12);
x_15 = lean_ctor_get(x_14, 1);
x_16 = l_Lean_IR_EmitC_toCType(x_15);
x_17 = lean_string_append(x_13, x_16);
lean_dec_ref(x_16);
x_3 = x_10;
x_4 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitFnDeclAux_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitFnDeclAux_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_54; 
x_28 = lean_ctor_get(x_4, 0);
x_29 = l_Lean_IR_Decl_name(x_1);
lean_inc_ref(x_28);
x_54 = l_Lean_Compiler_LCNF_isSimpleGroundDecl(x_28, x_29);
if (x_54 == 0)
{
uint8_t x_55; 
lean_inc_ref(x_28);
lean_inc_ref(x_28);
x_55 = l_Lean_isClosedTermName(x_28, x_29);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_83; 
x_56 = l_Lean_IR_Decl_params(x_1);
x_83 = l_Array_isEmpty___redArg(x_56);
if (x_83 == 0)
{
if (x_3 == 0)
{
goto block_82;
}
else
{
if (x_83 == 0)
{
x_57 = x_4;
x_58 = x_5;
goto block_79;
}
else
{
goto block_82;
}
}
}
else
{
if (x_3 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = ((lean_object*)(l_Lean_IR_EmitC_emitFnDeclAux___closed__3));
x_85 = lean_string_append(x_5, x_84);
x_57 = x_4;
x_58 = x_85;
goto block_79;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = ((lean_object*)(l_Lean_IR_EmitC_emitFnDeclAux___closed__4));
x_87 = lean_string_append(x_5, x_86);
x_57 = x_4;
x_58 = x_87;
goto block_79;
}
}
block_79:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_59 = l_Lean_IR_Decl_resultType(x_1);
x_60 = l_Lean_IR_EmitC_toCType(x_59);
lean_dec(x_59);
x_61 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__1));
x_62 = lean_string_append(x_60, x_61);
x_63 = lean_string_append(x_62, x_2);
lean_dec_ref(x_2);
x_64 = lean_string_append(x_58, x_63);
lean_dec_ref(x_63);
x_65 = l_Array_isEmpty___redArg(x_56);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = ((lean_object*)(l_Lean_IR_EmitC_emitFnDeclAux___closed__1));
x_67 = lean_string_append(x_64, x_66);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_array_get_size(x_56);
x_70 = ((lean_object*)(l_Lean_IR_EmitC_emitFnDeclAux___closed__2));
x_71 = lean_nat_dec_lt(x_68, x_69);
if (x_71 == 0)
{
lean_dec_ref(x_56);
x_38 = x_68;
x_39 = x_67;
x_40 = x_57;
x_41 = x_70;
goto block_53;
}
else
{
uint8_t x_72; 
x_72 = lean_nat_dec_le(x_69, x_69);
if (x_72 == 0)
{
if (x_71 == 0)
{
lean_dec_ref(x_56);
x_38 = x_68;
x_39 = x_67;
x_40 = x_57;
x_41 = x_70;
goto block_53;
}
else
{
size_t x_73; size_t x_74; lean_object* x_75; 
x_73 = 0;
x_74 = lean_usize_of_nat(x_69);
x_75 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__2(x_56, x_73, x_74, x_70);
lean_dec_ref(x_56);
x_38 = x_68;
x_39 = x_67;
x_40 = x_57;
x_41 = x_75;
goto block_53;
}
}
else
{
size_t x_76; size_t x_77; lean_object* x_78; 
x_76 = 0;
x_77 = lean_usize_of_nat(x_69);
x_78 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__2(x_56, x_76, x_77, x_70);
lean_dec_ref(x_56);
x_38 = x_68;
x_39 = x_67;
x_40 = x_57;
x_41 = x_78;
goto block_53;
}
}
}
else
{
lean_dec_ref(x_57);
lean_dec_ref(x_56);
lean_dec(x_29);
lean_dec_ref(x_28);
x_6 = x_64;
goto block_13;
}
}
block_82:
{
lean_object* x_80; lean_object* x_81; 
x_80 = ((lean_object*)(l_Lean_IR_EmitC_emitFnDeclAux___closed__3));
x_81 = lean_string_append(x_5, x_80);
x_57 = x_4;
x_58 = x_81;
goto block_79;
}
}
else
{
lean_object* x_88; 
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_4);
x_88 = l_Lean_IR_EmitC_emitFnClosedDecl___redArg(x_1, x_2, x_5);
return x_88;
}
}
else
{
lean_object* x_89; 
lean_dec(x_29);
x_89 = l_Lean_IR_EmitC_emitGroundDecl(x_1, x_2, x_4, x_5);
return x_89;
}
block_13:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__3));
x_8 = lean_string_append(x_6, x_7);
x_9 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_10 = lean_box(0);
x_11 = lean_string_append(x_8, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__3));
x_16 = lean_string_append(x_14, x_15);
x_6 = x_16;
goto block_13;
}
block_27:
{
lean_dec_ref(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_inc(x_19);
x_23 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitFnDeclAux_spec__0___redArg(x_18, x_19, x_19, x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec_ref(x_23);
x_14 = x_24;
goto block_17;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_19);
lean_dec_ref(x_18);
x_25 = ((lean_object*)(l_Lean_IR_EmitC_emitFnDeclAux___closed__0));
x_26 = lean_string_append(x_20, x_25);
x_14 = x_26;
goto block_17;
}
}
block_37:
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = l_Lean_closureMaxArgs;
x_34 = lean_array_get_size(x_32);
x_35 = lean_nat_dec_lt(x_33, x_34);
if (x_35 == 0)
{
lean_dec(x_29);
x_18 = x_32;
x_19 = x_34;
x_20 = x_30;
x_21 = x_31;
x_22 = x_35;
goto block_27;
}
else
{
uint8_t x_36; 
x_36 = l_Lean_Compiler_LCNF_isBoxedName(x_29);
lean_dec(x_29);
x_18 = x_32;
x_19 = x_34;
x_20 = x_30;
x_21 = x_31;
x_22 = x_36;
goto block_27;
}
}
block_53:
{
uint8_t x_42; 
lean_inc(x_29);
x_42 = l_Lean_isExternC(x_28, x_29);
if (x_42 == 0)
{
x_30 = x_39;
x_31 = x_40;
x_32 = x_41;
goto block_37;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_array_get_size(x_41);
x_44 = lean_mk_empty_array_with_capacity(x_38);
x_45 = lean_nat_dec_lt(x_38, x_43);
if (x_45 == 0)
{
lean_dec_ref(x_41);
x_30 = x_39;
x_31 = x_40;
x_32 = x_44;
goto block_37;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_43, x_43);
if (x_46 == 0)
{
if (x_45 == 0)
{
lean_dec_ref(x_41);
x_30 = x_39;
x_31 = x_40;
x_32 = x_44;
goto block_37;
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; 
x_47 = 0;
x_48 = lean_usize_of_nat(x_43);
x_49 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__1(x_41, x_47, x_48, x_44);
lean_dec_ref(x_41);
x_30 = x_39;
x_31 = x_40;
x_32 = x_49;
goto block_37;
}
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; 
x_50 = 0;
x_51 = lean_usize_of_nat(x_43);
x_52 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__1(x_41, x_50, x_51, x_44);
lean_dec_ref(x_41);
x_30 = x_39;
x_31 = x_40;
x_32 = x_52;
goto block_37;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_IR_EmitC_emitFnDeclAux(x_1, x_2, x_6, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitFnDeclAux_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitFnDeclAux_spec__0___redArg(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitFnDeclAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitFnDeclAux_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDecl(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_IR_Decl_name(x_1);
lean_inc_ref(x_3);
x_6 = l_Lean_IR_EmitC_toCName(x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = l_Lean_IR_EmitC_emitFnDeclAux(x_1, x_7, x_2, x_3, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_18; 
lean_dec_ref(x_3);
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
x_12 = x_6;
x_13 = x_18;
goto block_17;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_14; 
if (x_13 == 0)
{
x_14 = x_12;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_11);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_IR_EmitC_emitFnDecl(x_1, x_5, x_3, x_4);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitExternDeclAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_IR_Decl_name(x_1);
lean_inc_ref(x_5);
x_7 = l_Lean_isExternC(x_5, x_6);
x_8 = l_Lean_IR_EmitC_emitFnDeclAux(x_1, x_2, x_7, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitExternDeclAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitExternDeclAux(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_IR_EmitC_emitFnDecls_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_IR_Decl_name(x_3);
x_6 = l_Lean_NameSet_insert(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_IR_EmitC_emitFnDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___00Lean_IR_EmitC_emitFnDecls_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDecls_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_4, x_5);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_uget_borrowed(x_3, x_4);
lean_inc_ref(x_7);
lean_inc(x_17);
x_18 = l_Lean_IR_EmitC_getDecl(x_17, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDecls_spec__1___closed__1));
x_22 = l_Lean_IR_Decl_name(x_19);
lean_inc_ref(x_1);
x_23 = l_Lean_getExternNameFor(x_1, x_21, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = l_Lean_NameSet_contains(x_2, x_17);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; 
x_25 = 1;
lean_inc_ref(x_7);
x_26 = l_Lean_IR_EmitC_emitFnDecl(x_19, x_25, x_7, x_20);
lean_dec(x_19);
x_9 = x_26;
goto block_15;
}
else
{
lean_object* x_27; 
lean_inc_ref(x_7);
x_27 = l_Lean_IR_EmitC_emitFnDecl(x_19, x_16, x_7, x_20);
lean_dec(x_19);
x_9 = x_27;
goto block_15;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec_ref(x_23);
lean_inc_ref(x_7);
x_29 = l_Lean_IR_EmitC_emitExternDeclAux(x_19, x_28, x_7, x_20);
lean_dec(x_19);
x_9 = x_29;
goto block_15;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
x_38 = !lean_is_exclusive(x_18);
if (x_38 == 0)
{
x_32 = x_18;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
else
{
lean_object* x_39; 
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_6);
lean_ctor_set(x_39, 1, x_8);
return x_39;
}
block_15:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_4, x_12);
x_4 = x_13;
x_6 = x_10;
x_8 = x_11;
goto _start;
}
else
{
lean_dec_ref(x_7);
lean_dec_ref(x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDecls_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDecls_spec__1(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDecls(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_inc_ref(x_3);
x_4 = l_Lean_IR_getDecls(x_3);
x_5 = l_List_reverse___redArg(x_4);
x_6 = l_Lean_NameSet_empty;
x_7 = l_List_foldl___at___00Lean_IR_EmitC_emitFnDecls_spec__0(x_6, x_5);
lean_inc_ref(x_3);
x_8 = l_Lean_IR_collectUsedDecls(x_3, x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get_size(x_8);
x_11 = lean_box(0);
x_12 = lean_nat_dec_lt(x_9, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_2);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_10, x_10);
if (x_14 == 0)
{
if (x_12 == 0)
{
lean_object* x_15; 
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_2);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_10);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDecls_spec__1(x_3, x_7, x_8, x_16, x_17, x_11, x_1, x_2);
lean_dec_ref(x_8);
lean_dec(x_7);
return x_18;
}
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_10);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDecls_spec__1(x_3, x_7, x_8, x_19, x_20, x_11, x_1, x_2);
lean_dec_ref(x_8);
lean_dec(x_7);
return x_21;
}
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_IR_EmitC_emitMainFn_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_name_eq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_IR_EmitC_emitMainFn_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Lean_IR_EmitC_emitMainFn_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_EmitC_emitMainFn_spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedConstantInfo_default;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_string_append(x_2, x_5);
x_8 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_9 = lean_string_append(x_7, x_8);
x_1 = x_6;
x_2 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__14));
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(22u);
x_4 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__13));
x_5 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__12));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_76; 
x_60 = ((lean_object*)(l_Lean_IR_EmitC_toCName___closed__1));
lean_inc_ref(x_1);
x_76 = l_Lean_IR_EmitC_getDecl(x_60, x_1, x_2);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_178; 
x_78 = lean_ctor_get(x_76, 1);
x_178 = !lean_is_exclusive(x_76);
if (x_178 == 0)
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_76, 0);
lean_dec(x_179);
x_79 = x_76;
x_80 = x_178;
goto block_177;
}
else
{
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_box(0);
x_80 = x_178;
goto block_177;
}
block_177:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; uint8_t x_153; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_81 = lean_ctor_get(x_77, 1);
lean_inc_ref(x_81);
lean_dec_ref(x_77);
x_172 = lean_array_get_size(x_81);
x_173 = lean_unsigned_to_nat(2u);
x_174 = lean_nat_dec_eq(x_172, x_173);
if (x_174 == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_unsigned_to_nat(1u);
x_176 = lean_nat_dec_eq(x_172, x_175);
x_153 = x_176;
goto block_171;
}
else
{
x_153 = x_174;
goto block_171;
}
block_122:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_87 = lean_ctor_get(x_83, 0);
x_88 = lean_ctor_get(x_83, 1);
x_89 = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
x_90 = lean_ctor_get(x_89, 0);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_90, 2);
lean_inc(x_91);
lean_dec_ref(x_90);
x_92 = lean_box(0);
x_93 = lean_box(0);
lean_inc_ref(x_87);
x_94 = l_Lean_PersistentEnvExtension_getState___redArg(x_92, x_89, x_87, x_91, x_93);
lean_dec(x_91);
lean_inc(x_88);
x_95 = l_Lean_mkModuleInitializationFunctionName(x_88, x_94, x_86);
lean_dec(x_94);
x_96 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__16));
x_97 = lean_string_append(x_96, x_95);
lean_dec_ref(x_95);
x_98 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__17));
x_99 = lean_string_append(x_97, x_98);
x_100 = lean_string_append(x_82, x_99);
lean_dec_ref(x_99);
x_101 = lean_string_append(x_100, x_84);
x_102 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__18));
x_103 = lean_string_append(x_101, x_102);
x_104 = lean_string_append(x_103, x_84);
x_105 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__20));
x_106 = lean_box(0);
x_107 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__26));
x_108 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_107, x_104);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec_ref(x_108);
x_110 = lean_array_get_size(x_81);
lean_dec_ref(x_81);
x_111 = lean_unsigned_to_nat(2u);
x_112 = lean_nat_dec_eq(x_110, x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__27));
x_114 = lean_string_append(x_109, x_113);
x_115 = lean_string_append(x_114, x_84);
x_61 = x_106;
x_62 = x_105;
x_63 = x_84;
x_64 = x_85;
x_65 = x_83;
x_66 = x_115;
goto block_75;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_116 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__42));
x_117 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_116, x_109);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec_ref(x_117);
x_119 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__43));
x_120 = lean_string_append(x_118, x_119);
x_121 = lean_string_append(x_120, x_84);
x_61 = x_106;
x_62 = x_105;
x_63 = x_84;
x_64 = x_85;
x_65 = x_83;
x_66 = x_121;
goto block_75;
}
}
block_134:
{
lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_126 = l_Lean_Environment_header(x_123);
x_127 = lean_ctor_get_uint8(x_126, sizeof(void*)*7 + 4);
lean_dec_ref(x_126);
x_128 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__44));
x_129 = lean_string_append(x_125, x_128);
x_130 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_131 = lean_string_append(x_129, x_130);
if (x_127 == 0)
{
uint8_t x_132; 
x_132 = 2;
x_82 = x_131;
x_83 = x_124;
x_84 = x_130;
x_85 = x_123;
x_86 = x_132;
goto block_122;
}
else
{
uint8_t x_133; 
x_133 = 0;
x_82 = x_131;
x_83 = x_124;
x_84 = x_130;
x_85 = x_123;
x_86 = x_133;
goto block_122;
}
}
block_152:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_139 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__45));
x_140 = lean_string_append(x_138, x_139);
x_141 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_142 = lean_string_append(x_140, x_141);
x_143 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__46));
x_144 = lean_string_append(x_142, x_143);
x_145 = lean_string_append(x_144, x_141);
if (x_136 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__47));
x_147 = lean_string_append(x_145, x_146);
x_148 = lean_string_append(x_147, x_141);
x_123 = x_135;
x_124 = x_137;
x_125 = x_148;
goto block_134;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__48));
x_150 = lean_string_append(x_145, x_149);
x_151 = lean_string_append(x_150, x_141);
x_123 = x_135;
x_124 = x_137;
x_125 = x_151;
goto block_134;
}
}
block_171:
{
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
lean_dec_ref(x_81);
lean_dec_ref(x_1);
x_154 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__49));
if (x_80 == 0)
{
lean_ctor_set_tag(x_79, 1);
lean_ctor_set(x_79, 0, x_154);
x_155 = x_79;
goto block_156;
}
else
{
lean_object* x_157; 
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_78);
x_155 = x_157;
goto block_156;
}
block_156:
{
return x_155;
}
}
else
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_del_object(x_79);
x_158 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_158);
x_159 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__51));
x_160 = l_Lean_IR_usesModuleFrom(x_158, x_159);
x_161 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__52));
x_162 = lean_string_append(x_78, x_161);
x_163 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_164 = lean_string_append(x_162, x_163);
if (x_160 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__53));
x_166 = lean_string_append(x_164, x_165);
x_167 = lean_string_append(x_166, x_163);
x_135 = x_158;
x_136 = x_160;
x_137 = x_1;
x_138 = x_167;
goto block_152;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__54));
x_169 = lean_string_append(x_164, x_168);
x_170 = lean_string_append(x_169, x_163);
x_135 = x_158;
x_136 = x_160;
x_137 = x_1;
x_138 = x_170;
goto block_152;
}
}
}
}
}
else
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; uint8_t x_188; 
lean_dec(x_77);
lean_dec_ref(x_1);
x_180 = lean_ctor_get(x_76, 1);
x_188 = !lean_is_exclusive(x_76);
if (x_188 == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_76, 0);
lean_dec(x_189);
x_181 = x_76;
x_182 = x_188;
goto block_187;
}
else
{
lean_inc(x_180);
lean_dec(x_76);
x_181 = lean_box(0);
x_182 = x_188;
goto block_187;
}
block_187:
{
lean_object* x_183; lean_object* x_184; 
x_183 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__55));
if (x_182 == 0)
{
lean_ctor_set_tag(x_181, 1);
lean_ctor_set(x_181, 0, x_183);
x_184 = x_181;
goto block_185;
}
else
{
lean_object* x_186; 
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_180);
x_184 = x_186;
goto block_185;
}
block_185:
{
return x_184;
}
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_198; 
lean_dec_ref(x_1);
x_190 = lean_ctor_get(x_76, 0);
x_191 = lean_ctor_get(x_76, 1);
x_198 = !lean_is_exclusive(x_76);
if (x_198 == 0)
{
x_192 = x_76;
x_193 = x_198;
goto block_197;
}
else
{
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_76);
x_192 = lean_box(0);
x_193 = x_198;
goto block_197;
}
block_197:
{
lean_object* x_194; 
if (x_193 == 0)
{
x_194 = x_192;
goto block_195;
}
else
{
lean_object* x_196; 
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_190);
lean_ctor_set(x_196, 1, x_191);
x_194 = x_196;
goto block_195;
}
block_195:
{
return x_194;
}
}
}
block_41:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_39; 
lean_dec_ref(x_9);
x_12 = lean_string_append(x_6, x_11);
lean_dec_ref(x_11);
x_13 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__0));
x_14 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__1));
x_15 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__2));
x_16 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__3));
x_17 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__4));
lean_inc_ref(x_5);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_4);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_27, x_3);
lean_dec_ref(x_27);
x_29 = lean_ctor_get(x_28, 1);
x_39 = !lean_is_exclusive(x_28);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_28, 0);
lean_dec(x_40);
x_30 = x_28;
x_31 = x_39;
goto block_38;
}
else
{
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_string_append(x_29, x_5);
lean_dec_ref(x_5);
x_33 = lean_box(0);
x_34 = lean_string_append(x_32, x_8);
lean_dec_ref(x_8);
if (x_31 == 0)
{
lean_ctor_set(x_30, 1, x_34);
lean_ctor_set(x_30, 0, x_33);
x_35 = x_30;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
block_59:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_49 = l_Lean_ConstantInfo_type(x_48);
lean_dec_ref(x_48);
x_50 = l_Lean_Expr_getForallBody(x_49);
lean_dec_ref(x_49);
x_51 = l_Lean_Expr_appArg_x21(x_50);
lean_dec_ref(x_50);
x_52 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__5));
x_53 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__6));
x_54 = l_Lean_Expr_constName_x3f(x_51);
lean_dec_ref(x_51);
x_55 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__9));
x_56 = l_Option_instBEq_beq___at___00Lean_IR_EmitC_emitMainFn_spec__1(x_54, x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__10));
x_3 = x_44;
x_4 = x_43;
x_5 = x_42;
x_6 = x_53;
x_7 = x_45;
x_8 = x_46;
x_9 = x_47;
x_10 = x_52;
x_11 = x_57;
goto block_41;
}
else
{
lean_object* x_58; 
x_58 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__11));
x_3 = x_44;
x_4 = x_43;
x_5 = x_42;
x_6 = x_53;
x_7 = x_45;
x_8 = x_46;
x_9 = x_47;
x_10 = x_52;
x_11 = x_58;
goto block_41;
}
}
block_75:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_67 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__3));
x_68 = lean_string_append(x_66, x_67);
x_69 = lean_string_append(x_68, x_63);
x_70 = 0;
x_71 = l_Lean_Environment_find_x3f(x_64, x_60, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_obj_once(&l_Lean_IR_EmitC_emitMainFn___closed__15, &l_Lean_IR_EmitC_emitMainFn___closed__15_once, _init_l_Lean_IR_EmitC_emitMainFn___closed__15);
x_73 = l_panic___at___00Lean_IR_EmitC_emitMainFn_spec__2(x_72);
x_42 = x_67;
x_43 = x_61;
x_44 = x_69;
x_45 = x_62;
x_46 = x_63;
x_47 = x_65;
x_48 = x_73;
goto block_59;
}
else
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
lean_dec_ref(x_71);
x_42 = x_67;
x_43 = x_61;
x_44 = x_69;
x_45 = x_62;
x_46 = x_63;
x_47 = x_65;
x_48 = x_74;
goto block_59;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_EmitC_hasMainFn___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_IR_Decl_name(x_1);
x_3 = ((lean_object*)(l_Lean_IR_EmitC_toCName___closed__1));
x_4 = lean_name_eq(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_hasMainFn___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_EmitC_hasMainFn___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_hasMainFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = ((lean_object*)(l_Lean_IR_EmitC_hasMainFn___closed__0));
x_5 = l_Lean_IR_getDecls(x_3);
x_6 = l_List_any___redArg(x_5, x_4);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFnIfNeeded(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
lean_inc_ref(x_1);
x_3 = l_Lean_IR_EmitC_hasMainFn(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_14; 
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_3, 1);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_3, 0);
lean_dec(x_15);
x_7 = x_3;
x_8 = x_14;
goto block_13;
}
else
{
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_9);
x_10 = x_7;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_6);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec_ref(x_3);
x_17 = l_Lean_IR_EmitC_emitMainFn(x_1, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_24; lean_object* x_25; lean_object* x_33; 
x_7 = lean_array_uget_borrowed(x_1, x_2);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 1);
x_9 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__1));
if (x_8 == 0)
{
lean_object* x_38; 
x_38 = ((lean_object*)(l_panic___at___00Lean_IR_EmitC_toCType_spec__0___closed__0));
x_33 = x_38;
goto block_37;
}
else
{
lean_object* x_39; 
x_39 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__3));
x_33 = x_39;
goto block_37;
}
block_23:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_14 = 1;
lean_inc(x_12);
x_15 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_12, x_14);
x_16 = lean_string_append(x_13, x_15);
lean_dec_ref(x_15);
x_17 = lean_string_append(x_9, x_16);
lean_dec_ref(x_16);
x_18 = lean_box(0);
x_19 = lean_string_append(x_5, x_17);
lean_dec_ref(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_2, x_20);
x_2 = x_21;
x_4 = x_18;
x_5 = x_19;
goto _start;
}
block_32:
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
x_27 = lean_string_append(x_24, x_25);
lean_dec_ref(x_25);
x_28 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__0));
x_29 = lean_string_append(x_27, x_28);
if (x_26 == 0)
{
lean_object* x_30; 
x_30 = ((lean_object*)(l_panic___at___00Lean_IR_EmitC_toCType_spec__0___closed__0));
x_10 = x_29;
x_11 = x_30;
goto block_23;
}
else
{
lean_object* x_31; 
x_31 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__1));
x_10 = x_29;
x_11 = x_31;
goto block_23;
}
}
block_37:
{
uint8_t x_34; 
x_34 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 2);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = ((lean_object*)(l_panic___at___00Lean_IR_EmitC_toCType_spec__0___closed__0));
x_24 = x_33;
x_25 = x_35;
goto block_32;
}
else
{
lean_object* x_36; 
x_36 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___closed__2));
x_24 = x_33;
x_25 = x_36;
goto block_32;
}
}
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_5);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileHeader(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_12; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec_ref(x_1);
x_17 = ((lean_object*)(l_Lean_IR_EmitC_emitFileHeader___closed__22));
x_18 = lean_string_append(x_2, x_17);
x_19 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_20 = lean_string_append(x_18, x_19);
x_21 = ((lean_object*)(l_Lean_IR_EmitC_emitFileHeader___closed__23));
x_22 = 1;
x_23 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_16, x_22);
x_24 = lean_string_append(x_21, x_23);
lean_dec_ref(x_23);
x_25 = lean_string_append(x_20, x_24);
lean_dec_ref(x_24);
x_26 = lean_string_append(x_25, x_19);
x_27 = ((lean_object*)(l_Lean_IR_EmitC_emitFileHeader___closed__24));
x_28 = lean_string_append(x_26, x_27);
x_29 = l_Lean_Environment_imports(x_15);
lean_dec_ref(x_15);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get_size(x_29);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_dec_ref(x_29);
x_3 = x_28;
goto block_11;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_box(0);
x_34 = lean_nat_dec_le(x_31, x_31);
if (x_34 == 0)
{
if (x_32 == 0)
{
lean_dec_ref(x_29);
x_3 = x_28;
goto block_11;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_31);
x_37 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg(x_29, x_35, x_36, x_33, x_28);
lean_dec_ref(x_29);
x_12 = x_37;
goto block_14;
}
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_31);
x_40 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg(x_29, x_38, x_39, x_33, x_28);
lean_dec_ref(x_29);
x_12 = x_40;
goto block_14;
}
}
block_11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_5 = lean_string_append(x_3, x_4);
x_6 = ((lean_object*)(l_Lean_IR_EmitC_emitFileHeader___closed__0));
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_string_append(x_7, x_4);
x_9 = ((lean_object*)(l_Lean_IR_EmitC_emitFileHeader___closed__21));
x_10 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_9, x_8);
return x_10;
}
block_14:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
x_3 = x_13;
goto block_11;
}
else
{
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFileHeader_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileFooter___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_IR_EmitC_emitFileFooter___redArg___closed__1));
x_3 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileFooter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_emitFileFooter___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileFooter___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_emitFileFooter(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwUnknownVar___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = ((lean_object*)(l_Lean_IR_EmitC_throwUnknownVar___redArg___closed__0));
x_4 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
x_5 = l_Nat_reprFast(x_1);
x_6 = lean_string_append(x_4, x_5);
lean_dec_ref(x_5);
x_7 = lean_string_append(x_3, x_6);
lean_dec_ref(x_6);
x_8 = ((lean_object*)(l_Lean_IR_EmitC_getDecl___closed__1));
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwUnknownVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_throwUnknownVar___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwUnknownVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_throwUnknownVar(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Lean_IR_instBEqJoinPointId_beq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_IR_instHashableJoinPointId_hash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0___redArg(x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getJPParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0___redArg(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = ((lean_object*)(l_Lean_IR_EmitC_getJPParams___closed__0));
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getJPParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_getJPParams(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_IR_EmitC_getJPParams_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = l_Lean_IR_EmitC_toCType(x_2);
x_5 = lean_string_append(x_3, x_4);
lean_dec_ref(x_4);
x_6 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__1));
x_7 = lean_string_append(x_5, x_6);
x_8 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
x_9 = l_Nat_reprFast(x_1);
x_10 = lean_string_append(x_8, x_9);
lean_dec_ref(x_9);
x_11 = lean_string_append(x_7, x_10);
lean_dec_ref(x_10);
x_12 = ((lean_object*)(l_Lean_IR_EmitC_declareVar___redArg___closed__0));
x_13 = lean_box(0);
x_14 = lean_string_append(x_11, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_declareVar___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_declareVar___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_declareVar(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_declareParams_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_uget_borrowed(x_1, x_2);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_10 = l_Lean_IR_EmitC_declareVar___redArg(x_8, x_9, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_11;
x_5 = x_12;
goto _start;
}
else
{
return x_10;
}
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_5);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_declareParams_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_declareParams_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_1);
x_6 = lean_box(0);
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
if (x_7 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_declareParams_spec__0___redArg(x_1, x_11, x_12, x_6, x_3);
return x_13;
}
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_5);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_declareParams_spec__0___redArg(x_1, x_14, x_15, x_6, x_3);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_declareParams(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_declareParams_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_declareParams_spec__0___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_declareParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_declareParams_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVars(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 3);
x_9 = l_Lean_IR_isTailCallTo(x_8, x_1);
lean_dec_ref(x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_IR_EmitC_declareVar___redArg(x_5, x_6, x_4);
lean_dec(x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = 1;
x_1 = x_7;
x_2 = x_12;
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
lean_dec(x_7);
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
x_16 = x_10;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_23 = lean_box(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_4);
return x_24;
}
}
case 1:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_1, 3);
lean_inc(x_26);
lean_dec_ref(x_1);
x_27 = l_Lean_IR_EmitC_declareParams(x_25, x_3, x_4);
if (lean_obj_tag(x_27) == 0)
{
if (x_2 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_get_size(x_25);
lean_dec_ref(x_25);
x_31 = lean_nat_dec_lt(x_29, x_30);
x_1 = x_26;
x_2 = x_31;
x_4 = x_28;
goto _start;
}
else
{
lean_object* x_33; 
lean_dec_ref(x_25);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec_ref(x_27);
x_1 = x_26;
x_4 = x_33;
goto _start;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_43; 
lean_dec(x_26);
lean_dec_ref(x_25);
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
x_43 = !lean_is_exclusive(x_27);
if (x_43 == 0)
{
x_37 = x_27;
x_38 = x_43;
goto block_42;
}
else
{
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
x_37 = lean_box(0);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_38 == 0)
{
x_39 = x_37;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_36);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
default: 
{
uint8_t x_44; 
x_44 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_45;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_1);
x_47 = lean_box(x_2);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_4);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_IR_EmitC_declareVars(x_1, x_5, x_3, x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTag___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_IR_IRType_isObj(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_box(0);
x_6 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
x_7 = l_Nat_reprFast(x_1);
x_8 = lean_string_append(x_6, x_7);
lean_dec_ref(x_7);
x_9 = lean_string_append(x_3, x_8);
lean_dec_ref(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = ((lean_object*)(l_Lean_IR_EmitC_emitTag___redArg___closed__0));
x_12 = lean_string_append(x_3, x_11);
x_13 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
x_14 = l_Nat_reprFast(x_1);
x_15 = lean_string_append(x_13, x_14);
lean_dec_ref(x_14);
x_16 = lean_string_append(x_12, x_15);
lean_dec_ref(x_15);
x_17 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__3));
x_18 = lean_box(0);
x_19 = lean_string_append(x_16, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTag___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitTag___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitTag___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitTag(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isIf(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_fget(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_22; 
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
x_10 = x_7;
x_11 = x_22;
goto block_21;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec_ref(x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_array_fget_borrowed(x_1, x_13);
x_15 = l_Lean_IR_Alt_body(x_14);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_15);
lean_ctor_set(x_10, 0, x_9);
x_16 = x_10;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_15);
x_16 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_7);
x_23 = lean_box(0);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isIf___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_EmitC_isIf(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInc___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_13; 
if (x_3 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_dec_eq(x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__1));
x_13 = x_30;
goto block_27;
}
else
{
lean_object* x_31; 
x_31 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__2));
x_13 = x_31;
goto block_27;
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_dec_eq(x_2, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__3));
x_13 = x_34;
goto block_27;
}
else
{
lean_object* x_35; 
x_35 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__4));
x_13 = x_35;
goto block_27;
}
}
block_12:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_7 = lean_string_append(x_5, x_6);
x_8 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_9 = lean_box(0);
x_10 = lean_string_append(x_7, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
block_27:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_string_append(x_4, x_13);
lean_dec_ref(x_13);
x_15 = ((lean_object*)(l_Lean_IR_EmitC_emitFnDeclAux___closed__1));
x_16 = lean_string_append(x_14, x_15);
x_17 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
x_18 = l_Nat_reprFast(x_1);
x_19 = lean_string_append(x_17, x_18);
lean_dec_ref(x_18);
x_20 = lean_string_append(x_16, x_19);
lean_dec_ref(x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_dec_eq(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_24 = lean_string_append(x_20, x_23);
x_25 = l_Nat_reprFast(x_2);
x_26 = lean_string_append(x_24, x_25);
lean_dec_ref(x_25);
x_5 = x_26;
goto block_12;
}
else
{
lean_dec(x_2);
x_5 = x_20;
goto block_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInc___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = l_Lean_IR_EmitC_emitInc___redArg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInc(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitInc___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_IR_EmitC_emitInc(x_1, x_2, x_6, x_4, x_5);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDec___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_13; 
if (x_3 == 0)
{
lean_object* x_28; 
x_28 = ((lean_object*)(l_Lean_IR_EmitC_emitDec___redArg___closed__0));
x_13 = x_28;
goto block_27;
}
else
{
lean_object* x_29; 
x_29 = ((lean_object*)(l_Lean_IR_EmitC_emitDec___redArg___closed__1));
x_13 = x_29;
goto block_27;
}
block_12:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_7 = lean_string_append(x_5, x_6);
x_8 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_9 = lean_box(0);
x_10 = lean_string_append(x_7, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
block_27:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_string_append(x_4, x_13);
lean_dec_ref(x_13);
x_15 = ((lean_object*)(l_Lean_IR_EmitC_emitFnDeclAux___closed__1));
x_16 = lean_string_append(x_14, x_15);
x_17 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
x_18 = l_Nat_reprFast(x_1);
x_19 = lean_string_append(x_17, x_18);
lean_dec_ref(x_18);
x_20 = lean_string_append(x_16, x_19);
lean_dec_ref(x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_dec_eq(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_24 = lean_string_append(x_20, x_23);
x_25 = l_Nat_reprFast(x_2);
x_26 = lean_string_append(x_24, x_25);
lean_dec_ref(x_25);
x_5 = x_26;
goto block_12;
}
else
{
lean_dec(x_2);
x_5 = x_20;
goto block_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDec___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = l_Lean_IR_EmitC_emitDec___redArg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDec(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitDec___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_IR_EmitC_emitDec(x_1, x_2, x_6, x_4, x_5);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDel___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = ((lean_object*)(l_Lean_IR_EmitC_emitDel___redArg___closed__0));
x_4 = lean_string_append(x_2, x_3);
x_5 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
x_6 = l_Nat_reprFast(x_1);
x_7 = lean_string_append(x_5, x_6);
lean_dec_ref(x_6);
x_8 = lean_string_append(x_4, x_7);
lean_dec_ref(x_7);
x_9 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_10 = lean_string_append(x_8, x_9);
x_11 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_12 = lean_box(0);
x_13 = lean_string_append(x_10, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitDel___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitDel(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSetTag___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_4 = ((lean_object*)(l_Lean_IR_EmitC_emitSetTag___redArg___closed__0));
x_5 = lean_string_append(x_3, x_4);
x_6 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
x_7 = l_Nat_reprFast(x_1);
x_8 = lean_string_append(x_6, x_7);
lean_dec_ref(x_7);
x_9 = lean_string_append(x_5, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Nat_reprFast(x_2);
x_13 = lean_string_append(x_11, x_12);
lean_dec_ref(x_12);
x_14 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_15 = lean_string_append(x_13, x_14);
x_16 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_17 = lean_box(0);
x_18 = lean_string_append(x_15, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSetTag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitSetTag___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSetTag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitSetTag(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSet___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_29; 
x_5 = ((lean_object*)(l_Lean_IR_EmitC_emitSet___redArg___closed__0));
x_6 = lean_string_append(x_4, x_5);
x_7 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
x_8 = l_Nat_reprFast(x_1);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = lean_string_append(x_6, x_9);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Nat_reprFast(x_2);
x_14 = lean_string_append(x_12, x_13);
lean_dec_ref(x_13);
x_15 = lean_string_append(x_14, x_11);
x_16 = l_Lean_IR_EmitC_emitArg___redArg(x_3, x_15);
x_17 = lean_ctor_get(x_16, 1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_16, 0);
lean_dec(x_30);
x_18 = x_16;
x_19 = x_29;
goto block_28;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_21 = lean_string_append(x_17, x_20);
x_22 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_23 = lean_box(0);
x_24 = lean_string_append(x_21, x_22);
if (x_19 == 0)
{
lean_ctor_set(x_18, 1, x_24);
lean_ctor_set(x_18, 0, x_23);
x_25 = x_18;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitSet___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitSet(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitOffset___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = l_Nat_reprFast(x_2);
x_8 = lean_string_append(x_3, x_7);
lean_dec_ref(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = ((lean_object*)(l_Lean_IR_EmitC_emitOffset___redArg___closed__0));
x_11 = lean_string_append(x_3, x_10);
x_12 = l_Nat_reprFast(x_1);
x_13 = lean_string_append(x_11, x_12);
lean_dec_ref(x_12);
x_14 = lean_nat_dec_lt(x_4, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = ((lean_object*)(l_Lean_IR_EmitC_ctorScalarSizeStr___closed__1));
x_18 = lean_string_append(x_13, x_17);
x_19 = lean_box(0);
x_20 = l_Nat_reprFast(x_2);
x_21 = lean_string_append(x_18, x_20);
lean_dec_ref(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitOffset___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitOffset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitOffset(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUSet___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_5 = ((lean_object*)(l_Lean_IR_EmitC_emitUSet___redArg___closed__0));
x_6 = lean_string_append(x_4, x_5);
x_7 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
x_8 = l_Nat_reprFast(x_1);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = lean_string_append(x_6, x_9);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Nat_reprFast(x_2);
x_14 = lean_string_append(x_12, x_13);
lean_dec_ref(x_13);
x_15 = lean_string_append(x_14, x_11);
x_16 = l_Nat_reprFast(x_3);
x_17 = lean_string_append(x_7, x_16);
lean_dec_ref(x_16);
x_18 = lean_string_append(x_15, x_17);
lean_dec_ref(x_17);
x_19 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_20 = lean_string_append(x_18, x_19);
x_21 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_22 = lean_box(0);
x_23 = lean_string_append(x_20, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitUSet___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitUSet(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSSet___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_36; lean_object* x_37; 
x_36 = ((lean_object*)(l_Lean_IR_EmitC_emitSSet___redArg___closed__0));
x_37 = lean_string_append(x_6, x_36);
x_7 = x_37;
goto block_35;
}
case 9:
{
lean_object* x_38; lean_object* x_39; 
x_38 = ((lean_object*)(l_Lean_IR_EmitC_emitSSet___redArg___closed__1));
x_39 = lean_string_append(x_6, x_38);
x_7 = x_39;
goto block_35;
}
case 1:
{
lean_object* x_40; lean_object* x_41; 
x_40 = ((lean_object*)(l_Lean_IR_EmitC_emitSSet___redArg___closed__2));
x_41 = lean_string_append(x_6, x_40);
x_7 = x_41;
goto block_35;
}
case 2:
{
lean_object* x_42; lean_object* x_43; 
x_42 = ((lean_object*)(l_Lean_IR_EmitC_emitSSet___redArg___closed__3));
x_43 = lean_string_append(x_6, x_42);
x_7 = x_43;
goto block_35;
}
case 3:
{
lean_object* x_44; lean_object* x_45; 
x_44 = ((lean_object*)(l_Lean_IR_EmitC_emitSSet___redArg___closed__4));
x_45 = lean_string_append(x_6, x_44);
x_7 = x_45;
goto block_35;
}
case 4:
{
lean_object* x_46; lean_object* x_47; 
x_46 = ((lean_object*)(l_Lean_IR_EmitC_emitSSet___redArg___closed__5));
x_47 = lean_string_append(x_6, x_46);
x_7 = x_47;
goto block_35;
}
default: 
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = ((lean_object*)(l_Lean_IR_EmitC_emitSSet___redArg___closed__6));
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_6);
return x_49;
}
}
block_35:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_33; 
x_8 = ((lean_object*)(l_Lean_IR_EmitC_emitFnDeclAux___closed__1));
x_9 = lean_string_append(x_7, x_8);
x_10 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
x_11 = l_Nat_reprFast(x_1);
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_13 = lean_string_append(x_9, x_12);
lean_dec_ref(x_12);
x_14 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lean_IR_EmitC_emitOffset___redArg(x_2, x_3, x_15);
x_17 = lean_ctor_get(x_16, 1);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_16, 0);
lean_dec(x_34);
x_18 = x_16;
x_19 = x_33;
goto block_32;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_string_append(x_17, x_14);
x_21 = l_Nat_reprFast(x_4);
x_22 = lean_string_append(x_10, x_21);
lean_dec_ref(x_21);
x_23 = lean_string_append(x_20, x_22);
lean_dec_ref(x_22);
x_24 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_25 = lean_string_append(x_23, x_24);
x_26 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_27 = lean_box(0);
x_28 = lean_string_append(x_25, x_26);
if (x_19 == 0)
{
lean_ctor_set(x_18, 1, x_28);
lean_ctor_set(x_18, 0, x_27);
x_29 = x_18;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSSet___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_EmitC_emitSSet___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_EmitC_emitSSet___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_EmitC_emitSSet(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 1)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = lean_array_fget_borrowed(x_1, x_13);
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_array_fget_borrowed(x_2, x_13);
lean_dec(x_13);
x_17 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
lean_inc(x_15);
x_18 = l_Nat_reprFast(x_15);
x_19 = lean_string_append(x_17, x_18);
lean_dec_ref(x_18);
x_20 = lean_string_append(x_5, x_19);
lean_dec_ref(x_19);
x_21 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__2));
x_22 = lean_string_append(x_20, x_21);
lean_inc(x_16);
x_23 = l_Lean_IR_EmitC_emitArg___redArg(x_16, x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__3));
x_26 = lean_string_append(x_24, x_25);
x_27 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_28 = lean_string_append(x_26, x_27);
x_4 = x_11;
x_5 = x_28;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitJmp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_getJPParams(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_39; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_39 = !lean_is_exclusive(x_5);
if (x_39 == 0)
{
x_8 = x_5;
x_9 = x_39;
goto block_38;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_array_get_size(x_6);
x_12 = lean_nat_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_1);
x_13 = ((lean_object*)(l_Lean_IR_EmitC_emitJmp___closed__0));
if (x_9 == 0)
{
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_13);
x_14 = x_8;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_7);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_36; 
lean_del_object(x_8);
x_17 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0___redArg(x_6, x_2, x_10, x_10, x_7);
lean_dec(x_6);
x_18 = lean_ctor_get(x_17, 1);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_17, 0);
lean_dec(x_37);
x_19 = x_17;
x_20 = x_36;
goto block_35;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = ((lean_object*)(l_Lean_IR_EmitC_emitJmp___closed__1));
x_22 = lean_string_append(x_18, x_21);
x_23 = ((lean_object*)(l_Lean_IR_EmitC_emitJmp___closed__2));
x_24 = l_Nat_reprFast(x_1);
x_25 = lean_string_append(x_23, x_24);
lean_dec_ref(x_24);
x_26 = lean_string_append(x_22, x_25);
lean_dec_ref(x_25);
x_27 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__3));
x_28 = lean_string_append(x_26, x_27);
x_29 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_30 = lean_box(0);
x_31 = lean_string_append(x_28, x_29);
if (x_20 == 0)
{
lean_ctor_set(x_19, 1, x_31);
lean_ctor_set(x_19, 0, x_30);
x_32 = x_19;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_1);
x_40 = lean_ctor_get(x_5, 0);
x_41 = lean_ctor_get(x_5, 1);
x_48 = !lean_is_exclusive(x_5);
if (x_48 == 0)
{
x_42 = x_5;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_5);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitJmp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitJmp(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0___redArg(x_1, x_2, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitJmp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLhs___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
x_4 = l_Nat_reprFast(x_1);
x_5 = lean_string_append(x_3, x_4);
lean_dec_ref(x_4);
x_6 = lean_string_append(x_2, x_5);
lean_dec_ref(x_5);
x_7 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__2));
x_8 = lean_box(0);
x_9 = lean_string_append(x_6, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLhs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLhs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitLhs(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 1)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_19; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_3);
x_11 = lean_nat_sub(x_2, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_19 = lean_nat_dec_lt(x_5, x_12);
if (x_19 == 0)
{
x_13 = x_4;
goto block_18;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_21 = lean_string_append(x_4, x_20);
x_13 = x_21;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_fget_borrowed(x_1, x_12);
lean_dec(x_12);
lean_inc(x_14);
x_15 = l_Lean_IR_EmitC_emitArg___redArg(x_14, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_3 = x_10;
x_4 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0___redArg(x_1, x_4, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitArgs(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0___redArg(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitArgs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorScalarSize___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_IR_EmitC_ctorScalarSizeStr(x_1, x_2);
x_5 = lean_box(0);
x_6 = lean_string_append(x_3, x_4);
lean_dec_ref(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorScalarSize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitCtorScalarSize___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorScalarSize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitCtorScalarSize(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitAllocCtor___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_29; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = ((lean_object*)(l_Lean_IR_EmitC_emitAllocCtor___redArg___closed__0));
x_8 = lean_string_append(x_2, x_7);
x_9 = l_Nat_reprFast(x_3);
x_10 = lean_string_append(x_8, x_9);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Nat_reprFast(x_4);
x_14 = lean_string_append(x_12, x_13);
lean_dec_ref(x_13);
x_15 = lean_string_append(x_14, x_11);
x_16 = l_Lean_IR_EmitC_emitCtorScalarSize___redArg(x_5, x_6, x_15);
x_17 = lean_ctor_get(x_16, 1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_16, 0);
lean_dec(x_30);
x_18 = x_16;
x_19 = x_29;
goto block_28;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_21 = lean_string_append(x_17, x_20);
x_22 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_23 = lean_box(0);
x_24 = lean_string_append(x_21, x_22);
if (x_19 == 0)
{
lean_ctor_set(x_18, 1, x_24);
lean_ctor_set(x_18, 0, x_23);
x_25 = x_18;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitAllocCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitAllocCtor___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitAllocCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitAllocCtor(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 1)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = ((lean_object*)(l_Lean_IR_EmitC_emitSet___redArg___closed__0));
x_15 = lean_string_append(x_5, x_14);
x_16 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
lean_inc(x_1);
x_17 = l_Nat_reprFast(x_1);
x_18 = lean_string_append(x_16, x_17);
lean_dec_ref(x_17);
x_19 = lean_string_append(x_15, x_18);
lean_dec_ref(x_18);
x_20 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_21 = lean_string_append(x_19, x_20);
lean_inc(x_13);
x_22 = l_Nat_reprFast(x_13);
x_23 = lean_string_append(x_21, x_22);
lean_dec_ref(x_22);
x_24 = lean_string_append(x_23, x_20);
x_25 = lean_array_fget_borrowed(x_2, x_13);
lean_dec(x_13);
lean_inc(x_25);
x_26 = l_Lean_IR_EmitC_emitArg___redArg(x_25, x_24);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_29 = lean_string_append(x_27, x_28);
x_30 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_31 = lean_string_append(x_29, x_30);
x_4 = x_11;
x_5 = x_31;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorSetArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0___redArg(x_1, x_2, x_5, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorSetArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0___redArg(x_1, x_2, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitCtorSetArgs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_38; 
lean_inc(x_1);
x_6 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_5);
x_7 = lean_ctor_get(x_6, 1);
x_38 = !lean_is_exclusive(x_6);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_6, 0);
lean_dec(x_39);
x_8 = x_6;
x_9 = x_38;
goto block_37;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_34; uint8_t x_35; 
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
x_16 = lean_ctor_get(x_2, 3);
x_17 = lean_ctor_get(x_2, 4);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_eq(x_15, x_34);
if (x_35 == 0)
{
x_18 = x_35;
goto block_33;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_eq(x_16, x_34);
x_18 = x_36;
goto block_33;
}
block_13:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_IR_EmitC_emitAllocCtor___redArg(x_2, x_7);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_3, x_4, x_11);
return x_12;
}
block_33:
{
if (x_18 == 0)
{
lean_del_object(x_8);
goto block_13;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_17, x_19);
if (x_20 == 0)
{
lean_del_object(x_8);
goto block_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc(x_14);
lean_dec_ref(x_2);
lean_dec(x_1);
x_21 = ((lean_object*)(l_Lean_IR_EmitC_emitCtor___closed__0));
x_22 = lean_string_append(x_7, x_21);
x_23 = l_Nat_reprFast(x_14);
x_24 = lean_string_append(x_22, x_23);
lean_dec_ref(x_23);
x_25 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_26 = lean_string_append(x_24, x_25);
x_27 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_28 = lean_box(0);
x_29 = lean_string_append(x_26, x_27);
if (x_9 == 0)
{
lean_ctor_set(x_8, 1, x_29);
lean_ctor_set(x_8, 0, x_28);
x_30 = x_8;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitCtor(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 1)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_3);
x_11 = lean_nat_sub(x_2, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_13 = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg___closed__0));
x_14 = lean_string_append(x_4, x_13);
x_15 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
lean_inc(x_1);
x_16 = l_Nat_reprFast(x_1);
x_17 = lean_string_append(x_15, x_16);
lean_dec_ref(x_16);
x_18 = lean_string_append(x_14, x_17);
lean_dec_ref(x_17);
x_19 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Nat_reprFast(x_12);
x_22 = lean_string_append(x_20, x_21);
lean_dec_ref(x_21);
x_23 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_24 = lean_string_append(x_22, x_23);
x_25 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_26 = lean_string_append(x_24, x_25);
x_3 = x_10;
x_4 = x_26;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_51; 
x_6 = ((lean_object*)(l_Lean_IR_EmitC_emitReset___closed__0));
x_7 = lean_string_append(x_5, x_6);
x_8 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
lean_inc(x_3);
x_9 = l_Nat_reprFast(x_3);
x_10 = lean_string_append(x_8, x_9);
lean_dec_ref(x_9);
x_11 = lean_string_append(x_7, x_10);
x_12 = ((lean_object*)(l_Lean_IR_EmitC_emitReset___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_14 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_15 = lean_string_append(x_13, x_14);
lean_inc(x_2);
x_16 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg(x_3, x_2, x_2, x_15);
lean_dec(x_2);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__1));
x_19 = lean_string_append(x_17, x_18);
lean_inc(x_1);
x_20 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_string_append(x_21, x_10);
x_23 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__3));
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_14);
x_26 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__2));
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_string_append(x_27, x_14);
x_29 = ((lean_object*)(l_Lean_IR_EmitC_emitReset___closed__2));
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_string_append(x_30, x_10);
lean_dec_ref(x_10);
x_32 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_string_append(x_33, x_14);
x_35 = lean_string_append(x_34, x_18);
x_36 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_35);
x_37 = lean_ctor_get(x_36, 1);
x_51 = !lean_is_exclusive(x_36);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_36, 0);
lean_dec(x_52);
x_38 = x_36;
x_39 = x_51;
goto block_50;
}
else
{
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_box(0);
x_39 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = ((lean_object*)(l_Lean_IR_EmitC_emitReset___closed__3));
x_41 = lean_string_append(x_37, x_40);
x_42 = lean_string_append(x_41, x_14);
x_43 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__3));
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_box(0);
x_46 = lean_string_append(x_44, x_14);
if (x_39 == 0)
{
lean_ctor_set(x_38, 1, x_46);
lean_ctor_set(x_38, 0, x_45);
x_47 = x_38;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_46);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitReset(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___redArg(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitReset_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReuse(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_16 = ((lean_object*)(l_Lean_IR_EmitC_emitReuse___closed__0));
x_17 = lean_string_append(x_7, x_16);
x_18 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
x_19 = l_Nat_reprFast(x_2);
x_20 = lean_string_append(x_18, x_19);
lean_dec_ref(x_19);
x_21 = lean_string_append(x_17, x_20);
x_22 = ((lean_object*)(l_Lean_IR_EmitC_emitReset___closed__1));
x_23 = lean_string_append(x_21, x_22);
x_24 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_25 = lean_string_append(x_23, x_24);
x_26 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__1));
x_27 = lean_string_append(x_25, x_26);
lean_inc(x_1);
x_28 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec_ref(x_28);
lean_inc_ref(x_3);
x_30 = l_Lean_IR_EmitC_emitAllocCtor___redArg(x_3, x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__2));
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_string_append(x_33, x_24);
x_35 = lean_string_append(x_34, x_26);
lean_inc(x_1);
x_36 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_35);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_string_append(x_37, x_20);
lean_dec_ref(x_20);
x_39 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__3));
x_40 = lean_string_append(x_38, x_39);
x_41 = lean_string_append(x_40, x_24);
if (x_4 == 0)
{
lean_dec_ref(x_3);
x_8 = x_6;
x_9 = x_41;
goto block_15;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_42 = lean_ctor_get(x_3, 1);
lean_inc(x_42);
lean_dec_ref(x_3);
x_43 = ((lean_object*)(l_Lean_IR_EmitC_emitReuse___closed__1));
x_44 = lean_string_append(x_41, x_43);
lean_inc(x_1);
x_45 = l_Nat_reprFast(x_1);
x_46 = lean_string_append(x_18, x_45);
lean_dec_ref(x_45);
x_47 = lean_string_append(x_44, x_46);
lean_dec_ref(x_46);
x_48 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_49 = lean_string_append(x_47, x_48);
x_50 = l_Nat_reprFast(x_42);
x_51 = lean_string_append(x_49, x_50);
lean_dec_ref(x_50);
x_52 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_53 = lean_string_append(x_51, x_52);
x_54 = lean_string_append(x_53, x_24);
x_8 = x_6;
x_9 = x_54;
goto block_15;
}
block_15:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__3));
x_11 = lean_string_append(x_9, x_10);
x_12 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_5, x_8, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReuse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
x_9 = l_Lean_IR_EmitC_emitReuse(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitProj___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_28; 
x_5 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_4);
x_6 = lean_ctor_get(x_5, 1);
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_5, 0);
lean_dec(x_29);
x_7 = x_5;
x_8 = x_28;
goto block_27;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = ((lean_object*)(l_Lean_IR_EmitC_emitProj___redArg___closed__0));
x_10 = lean_string_append(x_6, x_9);
x_11 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
x_12 = l_Nat_reprFast(x_3);
x_13 = lean_string_append(x_11, x_12);
lean_dec_ref(x_12);
x_14 = lean_string_append(x_10, x_13);
lean_dec_ref(x_13);
x_15 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Nat_reprFast(x_2);
x_18 = lean_string_append(x_16, x_17);
lean_dec_ref(x_17);
x_19 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_20 = lean_string_append(x_18, x_19);
x_21 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_22 = lean_box(0);
x_23 = lean_string_append(x_20, x_21);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_23);
lean_ctor_set(x_7, 0, x_22);
x_24 = x_7;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitProj___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitProj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitProj(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUProj___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_28; 
x_5 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_4);
x_6 = lean_ctor_get(x_5, 1);
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_5, 0);
lean_dec(x_29);
x_7 = x_5;
x_8 = x_28;
goto block_27;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = ((lean_object*)(l_Lean_IR_EmitC_emitUProj___redArg___closed__0));
x_10 = lean_string_append(x_6, x_9);
x_11 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
x_12 = l_Nat_reprFast(x_3);
x_13 = lean_string_append(x_11, x_12);
lean_dec_ref(x_12);
x_14 = lean_string_append(x_10, x_13);
lean_dec_ref(x_13);
x_15 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Nat_reprFast(x_2);
x_18 = lean_string_append(x_16, x_17);
lean_dec_ref(x_17);
x_19 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_20 = lean_string_append(x_18, x_19);
x_21 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_22 = lean_box(0);
x_23 = lean_string_append(x_20, x_21);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_23);
lean_ctor_set(x_7, 0, x_22);
x_24 = x_7;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitUProj___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUProj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitUProj(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSProj___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_32; 
x_32 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_6);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = ((lean_object*)(l_Lean_IR_EmitC_emitSProj___redArg___closed__0));
x_35 = lean_string_append(x_33, x_34);
x_7 = x_35;
goto block_31;
}
case 9:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec_ref(x_32);
x_37 = ((lean_object*)(l_Lean_IR_EmitC_emitSProj___redArg___closed__1));
x_38 = lean_string_append(x_36, x_37);
x_7 = x_38;
goto block_31;
}
case 1:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_dec_ref(x_32);
x_40 = ((lean_object*)(l_Lean_IR_EmitC_emitSProj___redArg___closed__2));
x_41 = lean_string_append(x_39, x_40);
x_7 = x_41;
goto block_31;
}
case 2:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_dec_ref(x_32);
x_43 = ((lean_object*)(l_Lean_IR_EmitC_emitSProj___redArg___closed__3));
x_44 = lean_string_append(x_42, x_43);
x_7 = x_44;
goto block_31;
}
case 3:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_32, 1);
lean_inc(x_45);
lean_dec_ref(x_32);
x_46 = ((lean_object*)(l_Lean_IR_EmitC_emitSProj___redArg___closed__4));
x_47 = lean_string_append(x_45, x_46);
x_7 = x_47;
goto block_31;
}
case 4:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_32, 1);
lean_inc(x_48);
lean_dec_ref(x_32);
x_49 = ((lean_object*)(l_Lean_IR_EmitC_emitSProj___redArg___closed__5));
x_50 = lean_string_append(x_48, x_49);
x_7 = x_50;
goto block_31;
}
default: 
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_59; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_51 = lean_ctor_get(x_32, 1);
x_59 = !lean_is_exclusive(x_32);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_32, 0);
lean_dec(x_60);
x_52 = x_32;
x_53 = x_59;
goto block_58;
}
else
{
lean_inc(x_51);
lean_dec(x_32);
x_52 = lean_box(0);
x_53 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_54; lean_object* x_55; 
x_54 = ((lean_object*)(l_Lean_IR_EmitC_emitSSet___redArg___closed__6));
if (x_53 == 0)
{
lean_ctor_set_tag(x_52, 1);
lean_ctor_set(x_52, 0, x_54);
x_55 = x_52;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_51);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
block_31:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_29; 
x_8 = ((lean_object*)(l_Lean_IR_EmitC_emitFnDeclAux___closed__1));
x_9 = lean_string_append(x_7, x_8);
x_10 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
x_11 = l_Nat_reprFast(x_5);
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_13 = lean_string_append(x_9, x_12);
lean_dec_ref(x_12);
x_14 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lean_IR_EmitC_emitOffset___redArg(x_3, x_4, x_15);
x_17 = lean_ctor_get(x_16, 1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_16, 0);
lean_dec(x_30);
x_18 = x_16;
x_19 = x_29;
goto block_28;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_21 = lean_string_append(x_17, x_20);
x_22 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_23 = lean_box(0);
x_24 = lean_string_append(x_21, x_22);
if (x_19 == 0)
{
lean_ctor_set(x_18, 1, x_24);
lean_ctor_set(x_18, 0, x_23);
x_25 = x_18;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSProj___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_EmitC_emitSProj___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_EmitC_emitSProj___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSProj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_EmitC_emitSProj(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_IR_EmitC_toStringArgs_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
x_6 = x_1;
x_7 = x_14;
goto block_13;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_IR_EmitC_argToCString(x_4);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_8);
x_9 = x_6;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_2);
x_9 = x_12;
goto block_11;
}
block_11:
{
x_1 = x_5;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toStringArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_array_to_list(x_1);
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at___00Lean_IR_EmitC_toStringArgs_spec__0(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 1)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = lean_box(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_23; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_11 = l_Lean_IR_instInhabitedParam_default;
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_4, x_12);
lean_dec(x_4);
x_14 = lean_nat_sub(x_3, x_13);
x_15 = lean_nat_sub(x_14, x_12);
lean_dec(x_14);
x_28 = lean_array_get_borrowed(x_11, x_2, x_15);
x_29 = lean_ctor_get(x_28, 1);
x_30 = l_Lean_IR_IRType_isErased(x_29);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = l_Lean_IR_IRType_isVoid(x_29);
x_23 = x_31;
goto block_27;
}
else
{
x_23 = x_30;
goto block_27;
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_array_fget_borrowed(x_1, x_15);
lean_dec(x_15);
lean_inc(x_18);
x_19 = l_Lean_IR_EmitC_emitArg___redArg(x_18, x_17);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec_ref(x_19);
x_4 = x_13;
x_5 = x_16;
x_6 = x_20;
goto _start;
}
block_27:
{
if (x_23 == 0)
{
if (x_5 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_25 = lean_string_append(x_6, x_24);
x_16 = x_23;
x_17 = x_25;
goto block_22;
}
else
{
x_16 = x_23;
x_17 = x_6;
goto block_22;
}
}
else
{
lean_dec(x_15);
x_4 = x_13;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
x_8 = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0___redArg(x_1, x_2, x_3, x_4, x_7, x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSimpleExternalCall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_6 = lean_string_append(x_5, x_1);
x_7 = ((lean_object*)(l_Lean_IR_EmitC_emitFnDeclAux___closed__1));
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_array_get_size(x_3);
x_10 = 1;
x_11 = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0___redArg(x_3, x_2, x_9, x_9, x_10, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_24; 
x_12 = lean_ctor_get(x_11, 1);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_11, 0);
lean_dec(x_25);
x_13 = x_11;
x_14 = x_24;
goto block_23;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_16 = lean_string_append(x_12, x_15);
x_17 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_box(0);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_18);
lean_ctor_set(x_13, 0, x_19);
x_20 = x_13;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_18);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
x_34 = !lean_is_exclusive(x_11);
if (x_34 == 0)
{
x_28 = x_11;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSimpleExternalCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitSimpleExternalCall(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
x_10 = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_IR_EmitC_emitSimpleExternalCall_spec__0(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitExternCall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_16; lean_object* x_17; 
x_16 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDecls_spec__1___closed__1));
x_17 = l_Lean_getExternEntryFor(x_3, x_16);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
switch (lean_obj_tag(x_18)) {
case 2:
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_IR_EmitC_emitSimpleExternalCall(x_19, x_2, x_4, x_5, x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_19);
return x_20;
}
case 1:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_36; 
lean_dec(x_1);
x_21 = lean_ctor_get(x_18, 1);
x_36 = !lean_is_exclusive(x_18);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_18, 0);
lean_dec(x_37);
x_22 = x_18;
x_23 = x_36;
goto block_35;
}
else
{
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = l_Lean_IR_EmitC_toStringArgs(x_4);
x_25 = l_Lean_expandExternPattern(x_21, x_24);
lean_dec(x_24);
x_26 = lean_string_append(x_6, x_25);
lean_dec_ref(x_25);
x_27 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__3));
x_28 = lean_string_append(x_26, x_27);
x_29 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_30 = lean_box(0);
x_31 = lean_string_append(x_28, x_29);
if (x_23 == 0)
{
lean_ctor_set_tag(x_22, 0);
lean_ctor_set(x_22, 1, x_31);
lean_ctor_set(x_22, 0, x_30);
x_32 = x_22;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
default: 
{
lean_dec(x_18);
lean_dec_ref(x_4);
x_7 = x_6;
goto block_15;
}
}
}
else
{
lean_dec(x_17);
lean_dec_ref(x_4);
x_7 = x_6;
goto block_15;
}
block_15:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = ((lean_object*)(l_Lean_IR_EmitC_emitExternCall___closed__0));
x_9 = 1;
x_10 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_9);
x_11 = lean_string_append(x_8, x_10);
lean_dec_ref(x_10);
x_12 = ((lean_object*)(l_Lean_IR_EmitC_getDecl___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitExternCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_EmitC_emitExternCall(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_66; lean_object* x_67; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_70; 
x_70 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__3));
x_5 = x_70;
x_6 = x_3;
x_7 = x_4;
goto block_65;
}
case 9:
{
lean_object* x_71; 
x_71 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__4));
x_5 = x_71;
x_6 = x_3;
x_7 = x_4;
goto block_65;
}
case 1:
{
lean_object* x_72; 
x_72 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__5));
x_5 = x_72;
x_6 = x_3;
x_7 = x_4;
goto block_65;
}
case 2:
{
lean_object* x_73; 
x_73 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__6));
x_5 = x_73;
x_6 = x_3;
x_7 = x_4;
goto block_65;
}
case 3:
{
lean_object* x_74; 
x_74 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__7));
x_5 = x_74;
x_6 = x_3;
x_7 = x_4;
goto block_65;
}
case 4:
{
lean_object* x_75; 
x_75 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__8));
x_5 = x_75;
x_6 = x_3;
x_7 = x_4;
goto block_65;
}
case 5:
{
lean_object* x_76; 
x_76 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__9));
x_5 = x_76;
x_6 = x_3;
x_7 = x_4;
goto block_65;
}
case 7:
{
x_66 = x_3;
x_67 = x_4;
goto block_69;
}
case 8:
{
x_66 = x_3;
x_67 = x_4;
goto block_69;
}
case 12:
{
x_66 = x_3;
x_67 = x_4;
goto block_69;
}
case 13:
{
x_66 = x_3;
x_67 = x_4;
goto block_69;
}
default: 
{
lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec_ref(x_3);
x_77 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__10));
x_78 = 1;
x_79 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_78);
x_80 = lean_string_append(x_77, x_79);
lean_dec_ref(x_79);
x_81 = ((lean_object*)(l_Lean_IR_EmitC_getDecl___closed__1));
x_82 = lean_string_append(x_80, x_81);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_4);
return x_83;
}
}
block_65:
{
lean_object* x_8; 
lean_inc_ref(x_6);
lean_inc(x_2);
x_8 = l_Lean_IR_EmitC_toCName(x_2, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
lean_inc_ref(x_6);
lean_inc(x_2);
x_11 = l_Lean_IR_EmitC_toCName(x_2, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l_Lean_IR_EmitC_toCInitName(x_2, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_37; 
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_ctor_get(x_14, 1);
x_37 = !lean_is_exclusive(x_14);
if (x_37 == 0)
{
x_17 = x_14;
x_18 = x_37;
goto block_36;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_19 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__0));
x_20 = lean_string_append(x_5, x_19);
x_21 = lean_string_append(x_20, x_9);
lean_dec(x_9);
x_22 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__1));
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Lean_IR_EmitC_toTokenName(x_12);
x_25 = lean_string_append(x_23, x_24);
lean_dec_ref(x_24);
x_26 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_string_append(x_27, x_15);
lean_dec(x_15);
x_29 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__3));
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_box(0);
x_32 = lean_string_append(x_16, x_30);
lean_dec_ref(x_30);
if (x_18 == 0)
{
lean_ctor_set(x_17, 1, x_32);
lean_ctor_set(x_17, 0, x_31);
x_33 = x_17;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_5);
x_38 = lean_ctor_get(x_14, 0);
x_39 = lean_ctor_get(x_14, 1);
x_46 = !lean_is_exclusive(x_14);
if (x_46 == 0)
{
x_40 = x_14;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_14);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_ctor_get(x_11, 1);
x_55 = !lean_is_exclusive(x_11);
if (x_55 == 0)
{
x_49 = x_11;
x_50 = x_55;
goto block_54;
}
else
{
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_11);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_50 == 0)
{
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_48);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_64; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
x_56 = lean_ctor_get(x_8, 0);
x_57 = lean_ctor_get(x_8, 1);
x_64 = !lean_is_exclusive(x_8);
if (x_64 == 0)
{
x_58 = x_8;
x_59 = x_64;
goto block_63;
}
else
{
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_8);
x_58 = lean_box(0);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
if (x_59 == 0)
{
x_60 = x_58;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_57);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
}
block_69:
{
lean_object* x_68; 
x_68 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___closed__2));
x_5 = x_68;
x_6 = x_66;
x_7 = x_67;
goto block_65;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLeanFunReference(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_5);
x_6 = l_Lean_Compiler_LCNF_isSimpleGroundDecl(x_5, x_2);
if (x_6 == 0)
{
uint8_t x_7; 
lean_inc_ref(x_5);
x_7 = l_Lean_isClosedTermName(x_5, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_IR_EmitC_emitCName(x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitLeanFunReference_emitClosedTermRead(x_1, x_2, x_3, x_4);
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = l_Lean_IR_EmitC_toCName(x_2, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_25; 
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get(x_10, 1);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
x_13 = x_10;
x_14 = x_25;
goto block_24;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = ((lean_object*)(l_Lean_IR_EmitC_emitLeanFunReference___closed__0));
x_16 = lean_string_append(x_15, x_11);
lean_dec(x_11);
x_17 = ((lean_object*)(l_Lean_IR_EmitC_emitLeanFunReference___closed__1));
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_box(0);
x_20 = lean_string_append(x_12, x_18);
lean_dec_ref(x_18);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_20);
lean_ctor_set(x_13, 0, x_19);
x_21 = x_13;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
x_34 = !lean_is_exclusive(x_10);
if (x_34 == 0)
{
x_28 = x_10;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLeanFunReference___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitLeanFunReference(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFullApp_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = lean_ctor_get(x_11, 1);
x_13 = lean_ctor_get(x_12, 1);
x_14 = l_Lean_IR_IRType_isVoid(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_inc(x_11);
x_15 = lean_array_push(x_4, x_11);
x_5 = x_15;
goto block_9;
}
else
{
x_5 = x_4;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFullApp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFullApp_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFullApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_15; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_6);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec_ref(x_23);
lean_inc_ref(x_5);
lean_inc(x_3);
x_25 = l_Lean_IR_EmitC_getDecl(x_3, x_5, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_28);
lean_dec_ref(x_26);
lean_inc_ref(x_5);
x_29 = l_Lean_IR_EmitC_emitLeanFunReference(x_2, x_3, x_5, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec_ref(x_29);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_array_get_size(x_4);
x_43 = lean_nat_dec_lt(x_41, x_42);
if (x_43 == 0)
{
lean_dec_ref(x_28);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_15 = x_30;
goto block_22;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = l_Array_zip___redArg(x_4, x_28);
lean_dec_ref(x_28);
lean_dec_ref(x_4);
x_45 = lean_array_get_size(x_44);
x_46 = ((lean_object*)(l_Lean_IR_EmitC_emitFullApp___closed__0));
x_47 = lean_nat_dec_lt(x_41, x_45);
if (x_47 == 0)
{
lean_dec_ref(x_44);
x_31 = x_46;
goto block_40;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_45, x_45);
if (x_48 == 0)
{
if (x_47 == 0)
{
lean_dec_ref(x_44);
x_31 = x_46;
goto block_40;
}
else
{
size_t x_49; size_t x_50; lean_object* x_51; 
x_49 = 0;
x_50 = lean_usize_of_nat(x_45);
x_51 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFullApp_spec__0(x_44, x_49, x_50, x_46);
lean_dec_ref(x_44);
x_31 = x_51;
goto block_40;
}
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_45);
x_54 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFullApp_spec__0(x_44, x_52, x_53, x_46);
lean_dec_ref(x_44);
x_31 = x_54;
goto block_40;
}
}
}
block_40:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = l_Array_unzip___redArg(x_31);
lean_dec_ref(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = ((lean_object*)(l_Lean_IR_EmitC_emitFnDeclAux___closed__1));
x_35 = lean_string_append(x_30, x_34);
x_36 = l_Lean_IR_EmitC_emitArgs(x_33, x_5, x_35);
lean_dec_ref(x_5);
lean_dec(x_33);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__3));
x_39 = lean_string_append(x_37, x_38);
x_15 = x_39;
goto block_22;
}
}
else
{
lean_dec_ref(x_28);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_29;
}
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_26, 3);
if (lean_obj_tag(x_55) == 1)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 0);
if (lean_obj_tag(x_56) == 3)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 1);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_25, 1);
lean_inc(x_58);
lean_dec_ref(x_25);
x_59 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_59);
lean_dec_ref(x_26);
lean_inc_ref(x_5);
x_60 = l_Lean_IR_EmitC_emitLeanFunReference(x_2, x_3, x_5, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec_ref(x_60);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_array_get_size(x_4);
x_74 = lean_nat_dec_lt(x_72, x_73);
if (x_74 == 0)
{
lean_dec_ref(x_59);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_7 = x_61;
goto block_14;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = l_Array_zip___redArg(x_4, x_59);
lean_dec_ref(x_59);
lean_dec_ref(x_4);
x_76 = lean_array_get_size(x_75);
x_77 = ((lean_object*)(l_Lean_IR_EmitC_emitFullApp___closed__0));
x_78 = lean_nat_dec_lt(x_72, x_76);
if (x_78 == 0)
{
lean_dec_ref(x_75);
x_62 = x_77;
goto block_71;
}
else
{
uint8_t x_79; 
x_79 = lean_nat_dec_le(x_76, x_76);
if (x_79 == 0)
{
if (x_78 == 0)
{
lean_dec_ref(x_75);
x_62 = x_77;
goto block_71;
}
else
{
size_t x_80; size_t x_81; lean_object* x_82; 
x_80 = 0;
x_81 = lean_usize_of_nat(x_76);
x_82 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFullApp_spec__0(x_75, x_80, x_81, x_77);
lean_dec_ref(x_75);
x_62 = x_82;
goto block_71;
}
}
else
{
size_t x_83; size_t x_84; lean_object* x_85; 
x_83 = 0;
x_84 = lean_usize_of_nat(x_76);
x_85 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFullApp_spec__0(x_75, x_83, x_84, x_77);
lean_dec_ref(x_75);
x_62 = x_85;
goto block_71;
}
}
}
block_71:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = l_Array_unzip___redArg(x_62);
lean_dec_ref(x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = ((lean_object*)(l_Lean_IR_EmitC_emitFnDeclAux___closed__1));
x_66 = lean_string_append(x_61, x_65);
x_67 = l_Lean_IR_EmitC_emitArgs(x_64, x_5, x_66);
lean_dec_ref(x_5);
lean_dec(x_64);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__3));
x_70 = lean_string_append(x_68, x_69);
x_7 = x_70;
goto block_14;
}
}
else
{
lean_dec_ref(x_59);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_60;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_inc_ref(x_55);
x_86 = lean_ctor_get(x_25, 1);
lean_inc(x_86);
lean_dec_ref(x_25);
x_87 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_87);
lean_dec_ref(x_26);
x_88 = l_Lean_IR_EmitC_emitExternCall(x_3, x_87, x_55, x_4, x_5, x_86);
lean_dec_ref(x_5);
lean_dec_ref(x_87);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_inc_ref(x_55);
x_89 = lean_ctor_get(x_25, 1);
lean_inc(x_89);
lean_dec_ref(x_25);
x_90 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_90);
lean_dec_ref(x_26);
x_91 = l_Lean_IR_EmitC_emitExternCall(x_3, x_90, x_55, x_4, x_5, x_89);
lean_dec_ref(x_5);
lean_dec_ref(x_90);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_inc(x_55);
x_92 = lean_ctor_get(x_25, 1);
lean_inc(x_92);
lean_dec_ref(x_25);
x_93 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_93);
lean_dec_ref(x_26);
x_94 = l_Lean_IR_EmitC_emitExternCall(x_3, x_93, x_55, x_4, x_5, x_92);
lean_dec_ref(x_5);
lean_dec_ref(x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_103; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_95 = lean_ctor_get(x_25, 0);
x_96 = lean_ctor_get(x_25, 1);
x_103 = !lean_is_exclusive(x_25);
if (x_103 == 0)
{
x_97 = x_25;
x_98 = x_103;
goto block_102;
}
else
{
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_25);
x_97 = lean_box(0);
x_98 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_99; 
if (x_98 == 0)
{
x_99 = x_97;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_95);
lean_ctor_set(x_101, 1, x_96);
x_99 = x_101;
goto block_100;
}
block_100:
{
return x_99;
}
}
}
block_14:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__3));
x_9 = lean_string_append(x_7, x_8);
x_10 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_11 = lean_box(0);
x_12 = lean_string_append(x_9, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
block_22:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__3));
x_17 = lean_string_append(x_15, x_16);
x_18 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_19 = lean_box(0);
x_20 = lean_string_append(x_17, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFullApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_EmitC_emitFullApp(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 1)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_10 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_4, x_11);
lean_dec(x_4);
x_13 = lean_nat_sub(x_3, x_12);
x_14 = lean_nat_sub(x_13, x_11);
lean_dec(x_13);
x_15 = lean_array_fget_borrowed(x_1, x_14);
x_16 = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg___closed__0));
x_17 = lean_string_append(x_5, x_16);
x_18 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
lean_inc(x_2);
x_19 = l_Nat_reprFast(x_2);
x_20 = lean_string_append(x_18, x_19);
lean_dec_ref(x_19);
x_21 = lean_string_append(x_17, x_20);
lean_dec_ref(x_20);
x_22 = lean_string_append(x_21, x_10);
x_23 = l_Nat_reprFast(x_14);
x_24 = lean_string_append(x_22, x_23);
lean_dec_ref(x_23);
x_25 = lean_string_append(x_24, x_10);
lean_inc(x_15);
x_26 = l_Lean_IR_EmitC_emitArg___redArg(x_15, x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_29 = lean_string_append(x_27, x_28);
x_30 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_31 = lean_string_append(x_29, x_30);
x_4 = x_12;
x_5 = x_31;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitPartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc_ref(x_4);
lean_inc(x_2);
x_6 = l_Lean_IR_EmitC_getDecl(x_2, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
lean_inc(x_1);
x_9 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l_Lean_IR_EmitC_emitPartialApp___closed__0));
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Lean_IR_EmitC_emitCName(x_2, x_4, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_IR_Decl_params(x_7);
lean_dec(x_7);
x_16 = lean_array_get_size(x_15);
lean_dec_ref(x_15);
x_17 = ((lean_object*)(l_Lean_IR_EmitC_emitPartialApp___closed__1));
x_18 = lean_string_append(x_14, x_17);
x_19 = l_Nat_reprFast(x_16);
x_20 = lean_string_append(x_18, x_19);
lean_dec_ref(x_19);
x_21 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_array_get_size(x_3);
x_24 = l_Nat_reprFast(x_23);
x_25 = lean_string_append(x_22, x_24);
lean_dec_ref(x_24);
x_26 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_27 = lean_string_append(x_25, x_26);
x_28 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_29 = lean_string_append(x_27, x_28);
x_30 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg(x_3, x_1, x_23, x_23, x_29);
return x_30;
}
else
{
lean_dec(x_7);
lean_dec(x_1);
return x_13;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_ctor_get(x_6, 0);
x_32 = lean_ctor_get(x_6, 1);
x_39 = !lean_is_exclusive(x_6);
if (x_39 == 0)
{
x_33 = x_6;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_6);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_32);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitPartialApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitPartialApp(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___redArg(x_1, x_2, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitPartialApp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Lean_closureMaxArgs;
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_36; 
x_9 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_5);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l_Lean_IR_EmitC_emitApp___closed__0));
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Nat_reprFast(x_7);
x_14 = lean_string_append(x_12, x_13);
lean_dec_ref(x_13);
x_15 = ((lean_object*)(l_Lean_IR_EmitC_emitFnDeclAux___closed__1));
x_16 = lean_string_append(x_14, x_15);
x_17 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
x_18 = l_Nat_reprFast(x_2);
x_19 = lean_string_append(x_17, x_18);
lean_dec_ref(x_18);
x_20 = lean_string_append(x_16, x_19);
lean_dec_ref(x_19);
x_21 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Lean_IR_EmitC_emitArgs(x_3, x_4, x_22);
x_24 = lean_ctor_get(x_23, 1);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_23, 0);
lean_dec(x_37);
x_25 = x_23;
x_26 = x_36;
goto block_35;
}
else
{
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_28 = lean_string_append(x_24, x_27);
x_29 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_30 = lean_box(0);
x_31 = lean_string_append(x_28, x_29);
if (x_26 == 0)
{
lean_ctor_set(x_25, 1, x_31);
lean_ctor_set(x_25, 0, x_30);
x_32 = x_25;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_68; 
x_38 = ((lean_object*)(l_Lean_IR_EmitC_emitApp___closed__1));
x_39 = lean_string_append(x_5, x_38);
x_40 = l_Lean_IR_EmitC_emitArgs(x_3, x_4, x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = ((lean_object*)(l_Lean_IR_EmitC_emitApp___closed__2));
x_43 = lean_string_append(x_41, x_42);
x_44 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_45 = lean_string_append(x_43, x_44);
x_46 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_45);
x_47 = lean_ctor_get(x_46, 1);
x_68 = !lean_is_exclusive(x_46);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_46, 0);
lean_dec(x_69);
x_48 = x_46;
x_49 = x_68;
goto block_67;
}
else
{
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_box(0);
x_49 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_50 = ((lean_object*)(l_Lean_IR_EmitC_emitApp___closed__3));
x_51 = lean_string_append(x_47, x_50);
x_52 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
x_53 = l_Nat_reprFast(x_2);
x_54 = lean_string_append(x_52, x_53);
lean_dec_ref(x_53);
x_55 = lean_string_append(x_51, x_54);
lean_dec_ref(x_54);
x_56 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_57 = lean_string_append(x_55, x_56);
x_58 = l_Nat_reprFast(x_7);
x_59 = lean_string_append(x_57, x_58);
lean_dec_ref(x_58);
x_60 = ((lean_object*)(l_Lean_IR_EmitC_emitApp___closed__4));
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_box(0);
x_63 = lean_string_append(x_61, x_44);
if (x_49 == 0)
{
lean_ctor_set(x_48, 1, x_63);
lean_ctor_set(x_48, 0, x_62);
x_64 = x_48;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_63);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitApp(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBoxFn___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = ((lean_object*)(l_Lean_IR_EmitC_emitBoxFn___redArg___closed__0));
x_4 = lean_box(0);
x_5 = lean_string_append(x_2, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
case 3:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = ((lean_object*)(l_Lean_IR_EmitC_emitBoxFn___redArg___closed__1));
x_8 = lean_box(0);
x_9 = lean_string_append(x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
case 4:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = ((lean_object*)(l_Lean_IR_EmitC_emitBoxFn___redArg___closed__2));
x_12 = lean_box(0);
x_13 = lean_string_append(x_2, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
case 0:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = ((lean_object*)(l_Lean_IR_EmitC_emitBoxFn___redArg___closed__3));
x_16 = lean_box(0);
x_17 = lean_string_append(x_2, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
case 9:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = ((lean_object*)(l_Lean_IR_EmitC_emitBoxFn___redArg___closed__4));
x_20 = lean_box(0);
x_21 = lean_string_append(x_2, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
default: 
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = ((lean_object*)(l_Lean_IR_EmitC_emitBoxFn___redArg___closed__5));
x_24 = lean_box(0);
x_25 = lean_string_append(x_2, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBoxFn___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_emitBoxFn___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBoxFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitBoxFn___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBoxFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitBoxFn(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBox___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_26; 
x_5 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_IR_EmitC_emitBoxFn___redArg(x_3, x_6);
x_8 = lean_ctor_get(x_7, 1);
x_26 = !lean_is_exclusive(x_7);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_7, 0);
lean_dec(x_27);
x_9 = x_7;
x_10 = x_26;
goto block_25;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = ((lean_object*)(l_Lean_IR_EmitC_emitFnDeclAux___closed__1));
x_12 = lean_string_append(x_8, x_11);
x_13 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
x_14 = l_Nat_reprFast(x_2);
x_15 = lean_string_append(x_13, x_14);
lean_dec_ref(x_14);
x_16 = lean_string_append(x_12, x_15);
lean_dec_ref(x_15);
x_17 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_18 = lean_string_append(x_16, x_17);
x_19 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_20 = lean_box(0);
x_21 = lean_string_append(x_18, x_19);
if (x_10 == 0)
{
lean_ctor_set(x_9, 1, x_21);
lean_ctor_set(x_9, 0, x_20);
x_22 = x_9;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_21);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBox___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitBox___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBox(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitBox___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBox___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitBox(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnbox___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_26; 
x_5 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_4);
x_6 = lean_ctor_get(x_5, 1);
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_5, 0);
lean_dec(x_27);
x_7 = x_5;
x_8 = x_26;
goto block_25;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_9 = l_Lean_IR_getUnboxOpName(x_2);
x_10 = lean_string_append(x_6, x_9);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l_Lean_IR_EmitC_emitFnDeclAux___closed__1));
x_12 = lean_string_append(x_10, x_11);
x_13 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
x_14 = l_Nat_reprFast(x_3);
x_15 = lean_string_append(x_13, x_14);
lean_dec_ref(x_14);
x_16 = lean_string_append(x_12, x_15);
lean_dec_ref(x_15);
x_17 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_18 = lean_string_append(x_16, x_17);
x_19 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_20 = lean_box(0);
x_21 = lean_string_append(x_18, x_19);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_21);
lean_ctor_set(x_7, 0, x_20);
x_22 = x_7;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_21);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnbox___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitUnbox___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnbox(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitUnbox___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnbox___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitUnbox(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIsShared___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_23; 
x_4 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_3);
x_5 = lean_ctor_get(x_4, 1);
x_23 = !lean_is_exclusive(x_4);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_4, 0);
lean_dec(x_24);
x_6 = x_4;
x_7 = x_23;
goto block_22;
}
else
{
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = ((lean_object*)(l_Lean_IR_EmitC_emitIsShared___redArg___closed__0));
x_9 = lean_string_append(x_5, x_8);
x_10 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
x_11 = l_Nat_reprFast(x_2);
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_13 = lean_string_append(x_9, x_12);
lean_dec_ref(x_12);
x_14 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_15 = lean_string_append(x_13, x_14);
x_16 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_17 = lean_box(0);
x_18 = lean_string_append(x_15, x_16);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_18);
lean_ctor_set(x_6, 0, x_17);
x_19 = x_6;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIsShared(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitIsShared___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIsShared___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitIsShared(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitNumLit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_IR_IRType_isObj(x_1);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_cstr_to_nat("4294967296");
x_6 = lean_nat_dec_lt(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(5);
x_8 = l_Lean_IR_instBEqIRType_beq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Nat_reprFast(x_2);
x_10 = lean_string_append(x_3, x_9);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l_Lean_IR_EmitC_emitNumLit___redArg___closed__0));
x_12 = lean_box(0);
x_13 = lean_string_append(x_10, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = ((lean_object*)(l_Lean_IR_EmitC_emitNumLit___redArg___closed__1));
x_16 = lean_string_append(x_3, x_15);
x_17 = l_Nat_reprFast(x_2);
x_18 = lean_string_append(x_16, x_17);
lean_dec_ref(x_17);
x_19 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__2___closed__1));
x_20 = lean_box(0);
x_21 = lean_string_append(x_18, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = l_Nat_reprFast(x_2);
x_25 = lean_string_append(x_3, x_24);
lean_dec_ref(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_1);
x_27 = lean_cstr_to_nat("4294967296");
x_28 = lean_nat_dec_lt(x_2, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = ((lean_object*)(l_Lean_IR_EmitC_emitNumLit___redArg___closed__2));
x_30 = lean_string_append(x_3, x_29);
x_31 = l_Nat_reprFast(x_2);
x_32 = lean_string_append(x_30, x_31);
lean_dec_ref(x_31);
x_33 = ((lean_object*)(l_Lean_IR_EmitC_emitNumLit___redArg___closed__3));
x_34 = lean_box(0);
x_35 = lean_string_append(x_32, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = ((lean_object*)(l_Lean_IR_EmitC_emitNumLit___redArg___closed__4));
x_38 = lean_string_append(x_3, x_37);
x_39 = l_Nat_reprFast(x_2);
x_40 = lean_string_append(x_38, x_39);
lean_dec_ref(x_39);
x_41 = ((lean_object*)(l_Lean_IR_EmitC_emitNumLit___redArg___closed__5));
x_42 = lean_box(0);
x_43 = lean_string_append(x_40, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitNumLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitNumLit___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitNumLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitNumLit(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitLhs___redArg(x_1, x_4);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_21; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec_ref(x_3);
x_8 = l_Lean_IR_EmitC_emitNumLit___redArg(x_2, x_7, x_6);
x_9 = lean_ctor_get(x_8, 1);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_8, 0);
lean_dec(x_22);
x_10 = x_8;
x_11 = x_21;
goto block_20;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__3));
x_13 = lean_string_append(x_9, x_12);
x_14 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_15 = lean_box(0);
x_16 = lean_string_append(x_13, x_14);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_16);
lean_ctor_set(x_10, 0, x_15);
x_17 = x_10;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_49; 
lean_dec(x_2);
x_23 = lean_ctor_get(x_5, 1);
x_49 = !lean_is_exclusive(x_5);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_5, 0);
lean_dec(x_50);
x_24 = x_5;
x_25 = x_49;
goto block_48;
}
else
{
lean_inc(x_23);
lean_dec(x_5);
x_24 = lean_box(0);
x_25 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_26 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_26);
lean_dec_ref(x_3);
x_27 = ((lean_object*)(l_Lean_IR_EmitC_emitLit___redArg___closed__0));
x_28 = lean_string_append(x_23, x_27);
lean_inc_ref(x_26);
x_29 = l_Lean_IR_EmitC_quoteString(x_26);
x_30 = lean_string_append(x_28, x_29);
lean_dec_ref(x_29);
x_31 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_string_utf8_byte_size(x_26);
x_34 = l_Nat_reprFast(x_33);
x_35 = lean_string_append(x_32, x_34);
lean_dec_ref(x_34);
x_36 = lean_string_append(x_35, x_31);
x_37 = lean_string_length(x_26);
lean_dec_ref(x_26);
x_38 = l_Nat_reprFast(x_37);
x_39 = lean_string_append(x_36, x_38);
lean_dec_ref(x_38);
x_40 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_41 = lean_string_append(x_39, x_40);
x_42 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_43 = lean_box(0);
x_44 = lean_string_append(x_41, x_42);
if (x_25 == 0)
{
lean_ctor_set(x_24, 1, x_44);
lean_ctor_set(x_24, 0, x_43);
x_45 = x_24;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitLit___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitLit(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitVDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_3);
x_8 = l_Lean_IR_EmitC_emitCtor(x_1, x_6, x_7, x_4, x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec_ref(x_3);
x_11 = l_Lean_IR_EmitC_emitReset(x_1, x_9, x_10, x_4, x_5);
lean_dec_ref(x_4);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_15 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_15);
lean_dec_ref(x_3);
x_16 = l_Lean_IR_EmitC_emitReuse(x_1, x_12, x_13, x_14, x_15, x_4, x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_15);
return x_16;
}
case 3:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_4);
lean_dec(x_2);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_dec_ref(x_3);
x_19 = l_Lean_IR_EmitC_emitProj___redArg(x_1, x_17, x_18, x_5);
return x_19;
}
case 4:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_4);
lean_dec(x_2);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_dec_ref(x_3);
x_22 = l_Lean_IR_EmitC_emitUProj___redArg(x_1, x_20, x_21, x_5);
return x_22;
}
case 5:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_4);
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 2);
lean_inc(x_25);
lean_dec_ref(x_3);
x_26 = l_Lean_IR_EmitC_emitSProj___redArg(x_1, x_2, x_23, x_24, x_25, x_5);
lean_dec(x_2);
return x_26;
}
case 6:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_3, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_28);
lean_dec_ref(x_3);
x_29 = l_Lean_IR_EmitC_emitFullApp(x_1, x_2, x_27, x_28, x_4, x_5);
lean_dec(x_2);
return x_29;
}
case 7:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_30 = lean_ctor_get(x_3, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_31);
lean_dec_ref(x_3);
x_32 = l_Lean_IR_EmitC_emitPartialApp(x_1, x_30, x_31, x_4, x_5);
lean_dec_ref(x_31);
return x_32;
}
case 8:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_2);
x_33 = lean_ctor_get(x_3, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_34);
lean_dec_ref(x_3);
x_35 = l_Lean_IR_EmitC_emitApp(x_1, x_33, x_34, x_4, x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_34);
return x_35;
}
case 9:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_4);
lean_dec(x_2);
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
lean_dec_ref(x_3);
x_38 = l_Lean_IR_EmitC_emitBox___redArg(x_1, x_37, x_36, x_5);
lean_dec(x_36);
return x_38;
}
case 10:
{
lean_object* x_39; lean_object* x_40; 
lean_dec_ref(x_4);
x_39 = lean_ctor_get(x_3, 0);
lean_inc(x_39);
lean_dec_ref(x_3);
x_40 = l_Lean_IR_EmitC_emitUnbox___redArg(x_1, x_2, x_39, x_5);
lean_dec(x_2);
return x_40;
}
case 11:
{
lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_4);
x_41 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_41);
lean_dec_ref(x_3);
x_42 = l_Lean_IR_EmitC_emitLit___redArg(x_1, x_2, x_41, x_5);
return x_42;
}
default: 
{
lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_4);
lean_dec(x_2);
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
lean_dec_ref(x_3);
x_44 = l_Lean_IR_EmitC_emitIsShared___redArg(x_1, x_43, x_5);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isTailCall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
if (lean_obj_tag(x_2) == 6)
{
if (lean_obj_tag(x_3) == 10)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_28; 
x_12 = lean_ctor_get(x_2, 0);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_2, 1);
lean_dec(x_29);
x_13 = x_2;
x_14 = x_28;
goto block_27;
}
else
{
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_4, 3);
x_17 = lean_name_eq(x_12, x_16);
lean_dec(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(x_17);
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 0, x_18);
x_19 = x_13;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_5);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_IR_instBEqVarId_beq(x_1, x_15);
x_23 = lean_box(x_22);
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 0, x_23);
x_24 = x_13;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_5);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
else
{
lean_dec_ref(x_2);
x_6 = x_5;
goto block_10;
}
}
else
{
lean_dec_ref(x_2);
x_6 = x_5;
goto block_10;
}
}
else
{
lean_dec_ref(x_2);
x_6 = x_5;
goto block_10;
}
block_10:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isTailCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_isTailCall(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_EmitC_paramEqArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_IR_instBEqVarId_beq(x_4, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_paramEqArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_EmitC_paramEqArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 1)
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_IR_instInhabitedArg_default;
x_10 = lean_nat_sub(x_4, x_5);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_10);
x_12 = lean_array_get_borrowed(x_9, x_2, x_11);
lean_dec(x_11);
x_13 = l_Lean_IR_EmitC_paramEqArg(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_5, x_14);
lean_dec(x_5);
x_5 = x_15;
goto _start;
}
else
{
lean_dec(x_5);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 1)
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_nat_sub(x_4, x_5);
x_10 = lean_array_fget_borrowed(x_1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_9, x_11);
lean_dec(x_9);
x_13 = lean_nat_sub(x_2, x_12);
lean_inc(x_13);
x_14 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0___redArg(x_12, x_3, x_10, x_13, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_nat_sub(x_5, x_11);
lean_dec(x_5);
x_5 = x_15;
goto _start;
}
else
{
lean_dec(x_5);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 1)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_nat_sub(x_4, x_5);
x_10 = lean_array_fget_borrowed(x_1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_9, x_11);
lean_dec(x_9);
x_13 = lean_nat_sub(x_3, x_12);
lean_inc(x_13);
x_14 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0___redArg(x_12, x_2, x_10, x_13, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_nat_sub(x_5, x_11);
x_16 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1___redArg(x_1, x_3, x_2, x_4, x_15);
return x_16;
}
else
{
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_EmitC_overwriteParam(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1___redArg(x_1, x_2, x_3, x_3, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_overwriteParam___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_EmitC_overwriteParam(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00Lean_IR_EmitC_overwriteParam_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitTailCall_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_12, 1);
x_14 = l_Lean_IR_IRType_isVoid(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_inc(x_11);
x_15 = lean_array_push(x_4, x_11);
x_5 = x_15;
goto block_9;
}
else
{
x_5 = x_4;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitTailCall_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitTailCall_spec__3(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 1)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = lean_array_fget_borrowed(x_1, x_13);
x_15 = l_Lean_IR_instInhabitedArg_default;
x_16 = lean_array_get_borrowed(x_15, x_2, x_13);
x_17 = l_Lean_IR_EmitC_paramEqArg(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_14, 1);
x_19 = l_Lean_IR_EmitC_toCType(x_18);
x_20 = lean_string_append(x_5, x_19);
lean_dec_ref(x_19);
x_21 = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg___closed__0));
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Nat_reprFast(x_13);
x_24 = lean_string_append(x_22, x_23);
lean_dec_ref(x_23);
x_25 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__2));
x_26 = lean_string_append(x_24, x_25);
lean_inc(x_16);
x_27 = l_Lean_IR_EmitC_emitArg___redArg(x_16, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__3));
x_30 = lean_string_append(x_28, x_29);
x_31 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_32 = lean_string_append(x_30, x_31);
x_4 = x_11;
x_5 = x_32;
goto _start;
}
else
{
lean_dec(x_13);
x_4 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 1)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = lean_array_fget_borrowed(x_1, x_13);
x_15 = l_Lean_IR_instInhabitedArg_default;
x_16 = lean_array_get_borrowed(x_15, x_2, x_13);
x_17 = l_Lean_IR_EmitC_paramEqArg(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
lean_inc(x_18);
x_20 = l_Nat_reprFast(x_18);
x_21 = lean_string_append(x_19, x_20);
lean_dec_ref(x_20);
x_22 = lean_string_append(x_5, x_21);
lean_dec_ref(x_21);
x_23 = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg___closed__0));
x_24 = lean_string_append(x_22, x_23);
x_25 = l_Nat_reprFast(x_13);
x_26 = lean_string_append(x_24, x_25);
lean_dec_ref(x_25);
x_27 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__3));
x_28 = lean_string_append(x_26, x_27);
x_29 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_30 = lean_string_append(x_28, x_29);
x_4 = x_11;
x_5 = x_30;
goto _start;
}
else
{
lean_dec(x_13);
x_4 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 1)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = lean_array_fget_borrowed(x_1, x_13);
x_15 = l_Lean_IR_instInhabitedArg_default;
x_16 = lean_array_get_borrowed(x_15, x_2, x_13);
lean_dec(x_13);
x_17 = l_Lean_IR_EmitC_paramEqArg(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
lean_inc(x_18);
x_20 = l_Nat_reprFast(x_18);
x_21 = lean_string_append(x_19, x_20);
lean_dec_ref(x_20);
x_22 = lean_string_append(x_5, x_21);
lean_dec_ref(x_21);
x_23 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__2));
x_24 = lean_string_append(x_22, x_23);
lean_inc(x_16);
x_25 = l_Lean_IR_EmitC_emitArg___redArg(x_16, x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__3));
x_28 = lean_string_append(x_26, x_27);
x_29 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_30 = lean_string_append(x_28, x_29);
x_4 = x_11;
x_5 = x_30;
goto _start;
}
else
{
x_4 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTailCall(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_12; 
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_57; 
x_33 = lean_ctor_get(x_1, 1);
x_57 = !lean_is_exclusive(x_1);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_1, 0);
lean_dec(x_58);
x_34 = x_1;
x_35 = x_57;
goto block_56;
}
else
{
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_box(0);
x_35 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_2, 4);
x_37 = lean_array_get_size(x_36);
x_38 = lean_array_get_size(x_33);
x_39 = lean_nat_dec_eq(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_33);
x_40 = ((lean_object*)(l_Lean_IR_EmitC_emitTailCall___closed__2));
if (x_35 == 0)
{
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 1, x_3);
lean_ctor_set(x_34, 0, x_40);
x_41 = x_34;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_3);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_del_object(x_34);
x_44 = l_Array_zip___redArg(x_36, x_33);
lean_dec_ref(x_33);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_array_get_size(x_44);
x_47 = ((lean_object*)(l_Lean_IR_EmitC_emitTailCall___closed__3));
x_48 = lean_nat_dec_lt(x_45, x_46);
if (x_48 == 0)
{
lean_dec_ref(x_44);
x_12 = x_47;
goto block_32;
}
else
{
uint8_t x_49; 
x_49 = lean_nat_dec_le(x_46, x_46);
if (x_49 == 0)
{
if (x_48 == 0)
{
lean_dec_ref(x_44);
x_12 = x_47;
goto block_32;
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; 
x_50 = 0;
x_51 = lean_usize_of_nat(x_46);
x_52 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitTailCall_spec__3(x_44, x_50, x_51, x_47);
lean_dec_ref(x_44);
x_12 = x_52;
goto block_32;
}
}
else
{
size_t x_53; size_t x_54; lean_object* x_55; 
x_53 = 0;
x_54 = lean_usize_of_nat(x_46);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitTailCall_spec__3(x_44, x_53, x_54, x_47);
lean_dec_ref(x_44);
x_12 = x_55;
goto block_32;
}
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec_ref(x_1);
x_59 = ((lean_object*)(l_Lean_IR_EmitC_emitTailCall___closed__4));
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_3);
return x_60;
}
block_11:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = ((lean_object*)(l_Lean_IR_EmitC_emitTailCall___closed__0));
x_6 = lean_string_append(x_4, x_5);
x_7 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_8 = lean_box(0);
x_9 = lean_string_append(x_6, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
block_32:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l_Array_unzip___redArg(x_12);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_IR_EmitC_overwriteParam(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_array_get_size(x_14);
x_18 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0___redArg(x_14, x_15, x_17, x_17, x_3);
lean_dec(x_15);
lean_dec(x_14);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec_ref(x_18);
x_4 = x_19;
goto block_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = ((lean_object*)(l_Lean_IR_EmitC_emitTailCall___closed__1));
x_21 = lean_string_append(x_3, x_20);
x_22 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_array_get_size(x_14);
x_25 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg(x_14, x_15, x_24, x_24, x_23);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg(x_14, x_15, x_24, x_24, x_26);
lean_dec(x_15);
lean_dec(x_14);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__3));
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_string_append(x_30, x_22);
x_4 = x_31;
goto block_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTailCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitTailCall(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0___redArg(x_1, x_2, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___redArg(x_1, x_2, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___redArg(x_1, x_2, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitTailCall_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_2, x_3);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_array_uget_borrowed(x_1, x_2);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_ctor_get(x_15, 0);
x_17 = lean_ctor_get(x_15, 1);
x_18 = lean_ctor_get(x_16, 1);
x_19 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___closed__0));
x_20 = lean_string_append(x_6, x_19);
lean_inc(x_18);
x_21 = l_Nat_reprFast(x_18);
x_22 = lean_string_append(x_20, x_21);
lean_dec_ref(x_21);
x_23 = ((lean_object*)(l_Lean_IR_EmitC_emitJPs___closed__0));
x_24 = lean_string_append(x_22, x_23);
x_25 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_26 = lean_string_append(x_24, x_25);
lean_inc_ref(x_5);
lean_inc(x_17);
x_27 = l_Lean_IR_EmitC_emitFnBody(x_17, x_5, x_26);
x_7 = x_27;
goto block_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___closed__1));
x_30 = lean_string_append(x_6, x_29);
x_31 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_32 = lean_string_append(x_30, x_31);
lean_inc_ref(x_5);
lean_inc(x_28);
x_33 = l_Lean_IR_EmitC_emitFnBody(x_28, x_5, x_32);
x_7 = x_33;
goto block_13;
}
}
else
{
lean_object* x_34; 
lean_dec_ref(x_5);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_6);
return x_34;
}
block_13:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_8;
x_6 = x_9;
goto _start;
}
else
{
lean_dec_ref(x_5);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_14; lean_object* x_17; 
x_17 = l_Lean_IR_EmitC_isIf(x_3);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_3);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lean_IR_EmitC_emitIf(x_1, x_2, x_20, x_21, x_22, x_4, x_5);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_17);
x_24 = ((lean_object*)(l_Lean_IR_EmitC_emitCase___closed__0));
x_25 = lean_string_append(x_5, x_24);
x_26 = l_Lean_IR_EmitC_emitTag___redArg(x_1, x_2, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = ((lean_object*)(l_Lean_IR_EmitC_emitCase___closed__1));
x_29 = lean_string_append(x_27, x_28);
x_30 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_31 = lean_string_append(x_29, x_30);
x_32 = l_Lean_IR_ensureHasDefault(x_3);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_array_get_size(x_32);
x_35 = lean_nat_dec_lt(x_33, x_34);
if (x_35 == 0)
{
lean_dec_ref(x_32);
lean_dec_ref(x_4);
x_6 = x_31;
goto block_13;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_box(0);
x_37 = lean_nat_dec_le(x_34, x_34);
if (x_37 == 0)
{
if (x_35 == 0)
{
lean_dec_ref(x_32);
lean_dec_ref(x_4);
x_6 = x_31;
goto block_13;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_34);
x_40 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4(x_32, x_38, x_39, x_36, x_4, x_31);
lean_dec_ref(x_32);
x_14 = x_40;
goto block_16;
}
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; 
x_41 = 0;
x_42 = lean_usize_of_nat(x_34);
x_43 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4(x_32, x_41, x_42, x_36, x_4, x_31);
lean_dec_ref(x_32);
x_14 = x_43;
goto block_16;
}
}
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_26;
}
}
block_13:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__3));
x_8 = lean_string_append(x_6, x_7);
x_9 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_10 = lean_box(0);
x_11 = lean_string_append(x_8, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
block_16:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec_ref(x_14);
x_6 = x_15;
goto block_13;
}
else
{
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBlock(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
x_9 = l_Lean_IR_isTailCallTo(x_8, x_1);
lean_dec_ref(x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc_ref(x_2);
x_10 = l_Lean_IR_EmitC_emitVDecl(x_4, x_5, x_6, x_2, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec_ref(x_10);
x_1 = x_7;
x_3 = x_11;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_2);
return x_10;
}
}
else
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_13 = l_Lean_IR_EmitC_emitTailCall(x_6, x_2, x_3);
lean_dec_ref(x_2);
return x_13;
}
}
case 1:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_dec_ref(x_1);
x_1 = x_14;
goto _start;
}
case 2:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_dec_ref(x_1);
x_20 = l_Lean_IR_EmitC_emitSet___redArg(x_16, x_17, x_18, x_3);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_1 = x_19;
x_3 = x_21;
goto _start;
}
else
{
lean_dec(x_19);
lean_dec_ref(x_2);
return x_20;
}
}
case 3:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
lean_dec_ref(x_1);
x_26 = l_Lean_IR_EmitC_emitSetTag___redArg(x_23, x_24, x_3);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec_ref(x_26);
x_1 = x_25;
x_3 = x_27;
goto _start;
}
else
{
lean_dec(x_25);
lean_dec_ref(x_2);
return x_26;
}
}
case 4:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 3);
lean_inc(x_32);
lean_dec_ref(x_1);
x_33 = l_Lean_IR_EmitC_emitUSet___redArg(x_29, x_30, x_31, x_3);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec_ref(x_33);
x_1 = x_32;
x_3 = x_34;
goto _start;
}
else
{
lean_dec(x_32);
lean_dec_ref(x_2);
return x_33;
}
}
case 5:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 4);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 5);
lean_inc(x_41);
lean_dec_ref(x_1);
x_42 = l_Lean_IR_EmitC_emitSSet___redArg(x_36, x_37, x_38, x_39, x_40, x_3);
lean_dec(x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec_ref(x_42);
x_1 = x_41;
x_3 = x_43;
goto _start;
}
else
{
lean_dec(x_41);
lean_dec_ref(x_2);
return x_42;
}
}
case 6:
{
uint8_t x_45; 
x_45 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_49 = lean_ctor_get(x_1, 2);
lean_inc(x_49);
lean_dec_ref(x_1);
x_50 = l_Lean_IR_EmitC_emitInc___redArg(x_46, x_47, x_48, x_3);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec_ref(x_50);
x_1 = x_49;
x_3 = x_51;
goto _start;
}
else
{
lean_dec(x_49);
lean_dec_ref(x_2);
return x_50;
}
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_1, 2);
lean_inc(x_53);
lean_dec_ref(x_1);
x_1 = x_53;
goto _start;
}
}
case 7:
{
uint8_t x_55; 
x_55 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_59 = lean_ctor_get(x_1, 2);
lean_inc(x_59);
lean_dec_ref(x_1);
x_60 = l_Lean_IR_EmitC_emitDec___redArg(x_56, x_57, x_58, x_3);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec_ref(x_60);
x_1 = x_59;
x_3 = x_61;
goto _start;
}
else
{
lean_dec(x_59);
lean_dec_ref(x_2);
return x_60;
}
}
else
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_1, 2);
lean_inc(x_63);
lean_dec_ref(x_1);
x_1 = x_63;
goto _start;
}
}
case 8:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_1, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_1, 1);
lean_inc(x_66);
lean_dec_ref(x_1);
x_67 = l_Lean_IR_EmitC_emitDel___redArg(x_65, x_3);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec_ref(x_67);
x_1 = x_66;
x_3 = x_68;
goto _start;
}
else
{
lean_dec(x_66);
lean_dec_ref(x_2);
return x_67;
}
}
case 9:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_1, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_1, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_72);
lean_dec_ref(x_1);
x_73 = l_Lean_IR_EmitC_emitCase(x_70, x_71, x_72, x_2, x_3);
lean_dec(x_71);
return x_73;
}
case 10:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec_ref(x_2);
x_74 = lean_ctor_get(x_1, 0);
lean_inc(x_74);
lean_dec_ref(x_1);
x_75 = ((lean_object*)(l_Lean_IR_EmitC_emitBlock___closed__0));
x_76 = lean_string_append(x_3, x_75);
x_77 = l_Lean_IR_EmitC_emitArg___redArg(x_74, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_90; 
x_78 = lean_ctor_get(x_77, 1);
x_90 = !lean_is_exclusive(x_77);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_77, 0);
lean_dec(x_91);
x_79 = x_77;
x_80 = x_90;
goto block_89;
}
else
{
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_box(0);
x_80 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__3));
x_82 = lean_string_append(x_78, x_81);
x_83 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_84 = lean_box(0);
x_85 = lean_string_append(x_82, x_83);
if (x_80 == 0)
{
lean_ctor_set(x_79, 1, x_85);
lean_ctor_set(x_79, 0, x_84);
x_86 = x_79;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_85);
x_86 = x_88;
goto block_87;
}
block_87:
{
return x_86;
}
}
}
else
{
return x_77;
}
}
case 11:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_1, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_93);
lean_dec_ref(x_1);
x_94 = l_Lean_IR_EmitC_emitJmp(x_92, x_93, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_93);
return x_94;
}
default: 
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec_ref(x_2);
x_95 = ((lean_object*)(l_Lean_IR_EmitC_emitBlock___closed__1));
x_96 = lean_string_append(x_3, x_95);
x_97 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_98 = lean_box(0);
x_99 = lean_string_append(x_96, x_97);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitJPs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = ((lean_object*)(l_Lean_IR_EmitC_emitJmp___closed__2));
x_8 = l_Nat_reprFast(x_4);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = lean_string_append(x_3, x_9);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l_Lean_IR_EmitC_emitJPs___closed__0));
x_12 = lean_string_append(x_10, x_11);
x_13 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_14 = lean_string_append(x_12, x_13);
lean_inc_ref(x_2);
x_15 = l_Lean_IR_EmitC_emitFnBody(x_5, x_2, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_1 = x_6;
x_3 = x_16;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec_ref(x_2);
return x_15;
}
}
else
{
uint8_t x_18; 
x_18 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_24 = ((lean_object*)(l_Lean_IR_EmitC_emitTailCall___closed__1));
x_25 = lean_string_append(x_3, x_24);
x_26 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_27 = lean_string_append(x_25, x_26);
x_28 = 0;
lean_inc(x_1);
x_29 = l_Lean_IR_EmitC_declareVars(x_1, x_28, x_2, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec_ref(x_29);
x_4 = x_2;
x_5 = x_32;
goto block_23;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec_ref(x_29);
x_34 = lean_string_append(x_33, x_26);
x_4 = x_2;
x_5 = x_34;
goto block_23;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_43; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
x_43 = !lean_is_exclusive(x_29);
if (x_43 == 0)
{
x_37 = x_29;
x_38 = x_43;
goto block_42;
}
else
{
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_37 = lean_box(0);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_38 == 0)
{
x_39 = x_37;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_36);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
block_23:
{
lean_object* x_6; 
lean_inc_ref(x_4);
lean_inc(x_1);
x_6 = l_Lean_IR_EmitC_emitBlock(x_1, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_IR_EmitC_emitJPs(x_1, x_4, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_21; 
x_9 = lean_ctor_get(x_8, 1);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_8, 0);
lean_dec(x_22);
x_10 = x_8;
x_11 = x_21;
goto block_20;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__3));
x_13 = lean_string_append(x_9, x_12);
x_14 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_15 = lean_box(0);
x_16 = lean_string_append(x_13, x_14);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_16);
lean_ctor_set(x_10, 0, x_15);
x_17 = x_10;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
else
{
return x_8;
}
}
else
{
lean_dec_ref(x_4);
lean_dec(x_1);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = ((lean_object*)(l_Lean_IR_EmitC_emitIf___closed__0));
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Lean_IR_EmitC_emitTag___redArg(x_1, x_2, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = ((lean_object*)(l_Lean_IR_EmitC_emitIf___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Nat_reprFast(x_3);
x_15 = lean_string_append(x_13, x_14);
lean_dec_ref(x_14);
x_16 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__3));
x_17 = lean_string_append(x_15, x_16);
x_18 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_19 = lean_string_append(x_17, x_18);
lean_inc_ref(x_6);
x_20 = l_Lean_IR_EmitC_emitFnBody(x_4, x_6, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = ((lean_object*)(l_Lean_IR_EmitC_emitIf___closed__2));
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_string_append(x_23, x_18);
x_25 = l_Lean_IR_EmitC_emitFnBody(x_5, x_6, x_24);
return x_25;
}
else
{
lean_dec_ref(x_6);
lean_dec(x_5);
return x_20;
}
}
else
{
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_EmitC_emitIf(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitCase_spec__4(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCase___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitCase(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 1)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_27; 
x_9 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__1));
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_3, x_10);
lean_dec(x_3);
x_12 = lean_nat_sub(x_2, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_27 = lean_nat_dec_lt(x_5, x_13);
if (x_27 == 0)
{
x_14 = x_4;
goto block_26;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_compileCtor_spec__3___redArg___closed__1));
x_29 = lean_string_append(x_4, x_28);
x_14 = x_29;
goto block_26;
}
block_26:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_array_fget_borrowed(x_1, x_13);
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 0);
x_17 = lean_ctor_get(x_15, 1);
x_18 = l_Lean_IR_EmitC_toCType(x_17);
x_19 = lean_string_append(x_14, x_18);
lean_dec_ref(x_18);
x_20 = lean_string_append(x_19, x_9);
x_21 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
lean_inc(x_16);
x_22 = l_Nat_reprFast(x_16);
x_23 = lean_string_append(x_21, x_22);
lean_dec_ref(x_22);
x_24 = lean_string_append(x_20, x_23);
lean_dec_ref(x_23);
x_3 = x_11;
x_4 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 1)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_3);
x_11 = lean_nat_sub(x_2, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_13 = l_Lean_IR_instInhabitedParam_default;
x_14 = lean_array_get_borrowed(x_13, x_1, x_12);
x_15 = lean_ctor_get(x_14, 0);
x_16 = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__0));
x_17 = lean_string_append(x_4, x_16);
x_18 = ((lean_object*)(l_Lean_IR_EmitC_argToCString___closed__0));
lean_inc(x_15);
x_19 = l_Nat_reprFast(x_15);
x_20 = lean_string_append(x_18, x_19);
lean_dec_ref(x_19);
x_21 = lean_string_append(x_17, x_20);
lean_dec_ref(x_20);
x_22 = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__1));
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Nat_reprFast(x_12);
x_25 = lean_string_append(x_23, x_24);
lean_dec_ref(x_24);
x_26 = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__2));
x_27 = lean_string_append(x_25, x_26);
x_28 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_29 = lean_string_append(x_27, x_28);
x_3 = x_10;
x_4 = x_29;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_181; 
lean_inc_ref(x_1);
x_50 = l_Lean_IR_mkVarJPMaps(x_1);
x_51 = lean_ctor_get(x_50, 1);
x_181 = !lean_is_exclusive(x_50);
if (x_181 == 0)
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_50, 0);
lean_dec(x_182);
x_52 = x_50;
x_53 = x_181;
goto block_180;
}
else
{
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = x_181;
goto block_180;
}
block_39:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_36; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_7, 2);
x_36 = !lean_is_exclusive(x_7);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_7, 4);
lean_dec(x_37);
x_38 = lean_ctor_get(x_7, 3);
lean_dec(x_38);
x_12 = x_7;
x_13 = x_36;
goto block_35;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = ((lean_object*)(l_Lean_IR_EmitC_emitDeclAux___closed__0));
x_15 = lean_string_append(x_8, x_14);
x_16 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_17 = lean_string_append(x_15, x_16);
if (x_13 == 0)
{
lean_ctor_set(x_12, 4, x_4);
lean_ctor_set(x_12, 3, x_5);
x_18 = x_12;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_9);
lean_ctor_set(x_34, 1, x_10);
lean_ctor_set(x_34, 2, x_11);
lean_ctor_set(x_34, 3, x_5);
lean_ctor_set(x_34, 4, x_4);
x_18 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_19; 
x_19 = l_Lean_IR_EmitC_emitFnBody(x_6, x_18, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_31; 
x_20 = lean_ctor_get(x_19, 1);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_19, 0);
lean_dec(x_32);
x_21 = x_19;
x_22 = x_31;
goto block_30;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkHeader___redArg___closed__3));
x_24 = lean_string_append(x_20, x_23);
x_25 = lean_box(0);
x_26 = lean_string_append(x_24, x_16);
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_26);
lean_ctor_set(x_21, 0, x_25);
x_27 = x_21;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
return x_19;
}
}
}
}
block_49:
{
if (x_46 == 0)
{
lean_dec(x_42);
x_4 = x_41;
x_5 = x_43;
x_6 = x_44;
x_7 = x_40;
x_8 = x_45;
goto block_39;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_inc(x_42);
x_47 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg(x_41, x_42, x_42, x_45);
lean_dec(x_42);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec_ref(x_47);
x_4 = x_41;
x_5 = x_43;
x_6 = x_44;
x_7 = x_40;
x_8 = x_48;
goto block_39;
}
}
block_180:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_178; 
x_54 = lean_ctor_get(x_2, 0);
x_55 = lean_ctor_get(x_2, 1);
x_56 = lean_ctor_get(x_2, 3);
x_57 = lean_ctor_get(x_2, 4);
x_178 = !lean_is_exclusive(x_2);
if (x_178 == 0)
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_2, 2);
lean_dec(x_179);
x_58 = x_2;
x_59 = x_178;
goto block_177;
}
else
{
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_2);
x_58 = lean_box(0);
x_59 = x_178;
goto block_177;
}
block_177:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_139; uint8_t x_175; 
x_60 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_60);
lean_inc_ref(x_54);
x_175 = l_Lean_hasInitAttr(x_54, x_60);
if (x_175 == 0)
{
uint8_t x_176; 
lean_inc_ref(x_54);
x_176 = l_Lean_Compiler_LCNF_isSimpleGroundDecl(x_54, x_60);
x_139 = x_176;
goto block_174;
}
else
{
x_139 = x_175;
goto block_174;
}
block_74:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_66 = ((lean_object*)(l_Lean_IR_EmitC_emitDeclAux___closed__1));
x_67 = lean_string_append(x_65, x_66);
x_68 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_69 = lean_string_append(x_67, x_68);
x_70 = l_Lean_closureMaxArgs;
x_71 = lean_array_get_size(x_61);
x_72 = lean_nat_dec_lt(x_70, x_71);
if (x_72 == 0)
{
lean_dec(x_60);
x_40 = x_64;
x_41 = x_61;
x_42 = x_71;
x_43 = x_62;
x_44 = x_63;
x_45 = x_69;
x_46 = x_72;
goto block_49;
}
else
{
uint8_t x_73; 
x_73 = l_Lean_Compiler_LCNF_isBoxedName(x_60);
lean_dec(x_60);
x_40 = x_64;
x_41 = x_61;
x_42 = x_71;
x_43 = x_62;
x_44 = x_63;
x_45 = x_69;
x_46 = x_73;
goto block_49;
}
}
block_82:
{
lean_object* x_80; lean_object* x_81; 
x_80 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundArgToCLit___closed__3));
x_81 = lean_string_append(x_79, x_80);
x_61 = x_75;
x_62 = x_76;
x_63 = x_77;
x_64 = x_78;
x_65 = x_81;
goto block_74;
}
block_95:
{
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_inc(x_83);
x_91 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__1___redArg(x_89, x_83, x_83, x_86);
lean_dec(x_83);
lean_dec_ref(x_89);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec_ref(x_91);
x_75 = x_84;
x_76 = x_85;
x_77 = x_88;
x_78 = x_87;
x_79 = x_92;
goto block_82;
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec_ref(x_89);
lean_dec(x_83);
x_93 = ((lean_object*)(l_Lean_IR_EmitC_emitDeclAux___closed__2));
x_94 = lean_string_append(x_86, x_93);
x_75 = x_84;
x_76 = x_85;
x_77 = x_88;
x_78 = x_87;
x_79 = x_94;
goto block_82;
}
}
block_110:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_103 = lean_string_append(x_98, x_96);
lean_dec_ref(x_96);
x_104 = ((lean_object*)(l_Lean_IR_EmitC_emitFnDeclAux___closed__1));
x_105 = lean_string_append(x_103, x_104);
x_106 = l_Lean_closureMaxArgs;
x_107 = lean_array_get_size(x_102);
x_108 = lean_nat_dec_lt(x_106, x_107);
if (x_108 == 0)
{
x_83 = x_107;
x_84 = x_97;
x_85 = x_99;
x_86 = x_105;
x_87 = x_100;
x_88 = x_101;
x_89 = x_102;
x_90 = x_108;
goto block_95;
}
else
{
uint8_t x_109; 
x_109 = l_Lean_Compiler_LCNF_isBoxedName(x_60);
x_83 = x_107;
x_84 = x_97;
x_85 = x_99;
x_86 = x_105;
x_87 = x_100;
x_88 = x_101;
x_89 = x_102;
x_90 = x_109;
goto block_95;
}
}
block_138:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_118 = l_Lean_IR_EmitC_toCType(x_114);
lean_dec(x_114);
x_119 = lean_string_append(x_117, x_118);
lean_dec_ref(x_118);
x_120 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__1));
x_121 = lean_string_append(x_119, x_120);
x_122 = lean_unsigned_to_nat(0u);
x_123 = lean_array_get_size(x_112);
x_124 = lean_nat_dec_lt(x_122, x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = ((lean_object*)(l_Lean_IR_EmitC_toCInitName___closed__0));
x_126 = lean_string_append(x_125, x_111);
lean_dec_ref(x_111);
x_127 = ((lean_object*)(l_Lean_IR_EmitC_emitDeclAux___closed__3));
x_128 = lean_string_append(x_126, x_127);
x_129 = lean_string_append(x_121, x_128);
lean_dec_ref(x_128);
x_61 = x_112;
x_62 = x_113;
x_63 = x_115;
x_64 = x_116;
x_65 = x_129;
goto block_74;
}
else
{
lean_object* x_130; 
x_130 = ((lean_object*)(l_Lean_IR_EmitC_emitFnDeclAux___closed__2));
if (x_124 == 0)
{
x_96 = x_111;
x_97 = x_112;
x_98 = x_121;
x_99 = x_113;
x_100 = x_116;
x_101 = x_115;
x_102 = x_130;
goto block_110;
}
else
{
uint8_t x_131; 
x_131 = lean_nat_dec_le(x_123, x_123);
if (x_131 == 0)
{
if (x_124 == 0)
{
x_96 = x_111;
x_97 = x_112;
x_98 = x_121;
x_99 = x_113;
x_100 = x_116;
x_101 = x_115;
x_102 = x_130;
goto block_110;
}
else
{
size_t x_132; size_t x_133; lean_object* x_134; 
x_132 = 0;
x_133 = lean_usize_of_nat(x_123);
x_134 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__2(x_112, x_132, x_133, x_130);
x_96 = x_111;
x_97 = x_112;
x_98 = x_121;
x_99 = x_113;
x_100 = x_116;
x_101 = x_115;
x_102 = x_134;
goto block_110;
}
}
else
{
size_t x_135; size_t x_136; lean_object* x_137; 
x_135 = 0;
x_136 = lean_usize_of_nat(x_123);
x_137 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitFnDeclAux_spec__2(x_112, x_135, x_136, x_130);
x_96 = x_111;
x_97 = x_112;
x_98 = x_121;
x_99 = x_113;
x_100 = x_116;
x_101 = x_115;
x_102 = x_137;
goto block_110;
}
}
}
}
block_174:
{
if (x_139 == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_del_object(x_52);
x_140 = lean_ctor_get(x_1, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_141);
x_142 = lean_ctor_get(x_1, 2);
lean_inc(x_142);
x_143 = lean_ctor_get(x_1, 3);
lean_inc(x_143);
lean_dec_ref(x_1);
if (x_59 == 0)
{
lean_ctor_set(x_58, 2, x_51);
x_144 = x_58;
goto block_164;
}
else
{
lean_object* x_165; 
x_165 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_165, 0, x_54);
lean_ctor_set(x_165, 1, x_55);
lean_ctor_set(x_165, 2, x_51);
lean_ctor_set(x_165, 3, x_56);
lean_ctor_set(x_165, 4, x_57);
x_144 = x_165;
goto block_164;
}
block_164:
{
lean_object* x_145; 
lean_inc_ref(x_144);
lean_inc(x_140);
x_145 = l_Lean_IR_EmitC_toCName(x_140, x_144, x_3);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec_ref(x_145);
x_148 = lean_array_get_size(x_141);
x_149 = lean_unsigned_to_nat(0u);
x_150 = lean_nat_dec_eq(x_148, x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = ((lean_object*)(l_Lean_IR_EmitC_emitFnDeclAux___closed__3));
x_152 = lean_string_append(x_147, x_151);
x_111 = x_146;
x_112 = x_141;
x_113 = x_140;
x_114 = x_142;
x_115 = x_143;
x_116 = x_144;
x_117 = x_152;
goto block_138;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = ((lean_object*)(l_Lean_IR_EmitC_emitFnClosedDecl___redArg___closed__2));
x_154 = lean_string_append(x_147, x_153);
x_111 = x_146;
x_112 = x_141;
x_113 = x_140;
x_114 = x_142;
x_115 = x_143;
x_116 = x_144;
x_117 = x_154;
goto block_138;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_163; 
lean_dec_ref(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec(x_140);
lean_dec(x_60);
x_155 = lean_ctor_get(x_145, 0);
x_156 = lean_ctor_get(x_145, 1);
x_163 = !lean_is_exclusive(x_145);
if (x_163 == 0)
{
x_157 = x_145;
x_158 = x_163;
goto block_162;
}
else
{
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_145);
x_157 = lean_box(0);
x_158 = x_163;
goto block_162;
}
block_162:
{
lean_object* x_159; 
if (x_158 == 0)
{
x_159 = x_157;
goto block_160;
}
else
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_155);
lean_ctor_set(x_161, 1, x_156);
x_159 = x_161;
goto block_160;
}
block_160:
{
return x_159;
}
}
}
}
}
else
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_60);
lean_del_object(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_51);
lean_dec_ref(x_1);
x_166 = lean_box(0);
if (x_53 == 0)
{
lean_ctor_set(x_52, 1, x_3);
lean_ctor_set(x_52, 0, x_166);
x_167 = x_52;
goto block_168;
}
else
{
lean_object* x_169; 
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_3);
x_167 = x_169;
goto block_168;
}
block_168:
{
return x_167;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_60);
lean_del_object(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_51);
lean_dec_ref(x_1);
x_170 = lean_box(0);
if (x_53 == 0)
{
lean_ctor_set(x_52, 1, x_3);
lean_ctor_set(x_52, 0, x_170);
x_171 = x_52;
goto block_172;
}
else
{
lean_object* x_173; 
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_3);
x_171 = x_173;
goto block_172;
}
block_172:
{
return x_171;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__1___redArg(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_IR_Decl_normalizeIds(x_1);
lean_inc_ref(x_4);
x_5 = l_Lean_IR_EmitC_emitDeclAux(x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_dec_ref(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_18; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
x_8 = x_5;
x_9 = x_18;
goto block_17;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = ((lean_object*)(l_Lean_IR_EmitC_emitDecl___closed__0));
x_11 = lean_string_append(x_6, x_10);
x_12 = l_Lean_IR_declToString(x_4);
x_13 = lean_string_append(x_11, x_12);
lean_dec_ref(x_12);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_13);
x_14 = x_8;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_7);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_EmitC_emitFns_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec_ref(x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_8 = l_Lean_IR_EmitC_emitDecl(x_6, x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_1 = x_7;
x_3 = x_9;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFns(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = l_Lean_IR_getDecls(x_3);
x_5 = l_List_reverse___redArg(x_4);
x_6 = l_List_forM___at___00Lean_IR_EmitC_emitFns_spec__0(x_5, x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMarkPersistent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_IR_Decl_resultType(x_1);
x_6 = l_Lean_IR_IRType_isObj(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = ((lean_object*)(l_Lean_IR_EmitC_emitMarkPersistent___closed__0));
x_10 = lean_string_append(x_4, x_9);
x_11 = l_Lean_IR_EmitC_emitCName(x_2, x_3, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_24; 
x_12 = lean_ctor_get(x_11, 1);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_11, 0);
lean_dec(x_25);
x_13 = x_11;
x_14 = x_24;
goto block_23;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = ((lean_object*)(l_Lean_IR_EmitC_emitInc___redArg___closed__0));
x_16 = lean_string_append(x_12, x_15);
x_17 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_18 = lean_box(0);
x_19 = lean_string_append(x_16, x_17);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_19);
lean_ctor_set(x_13, 0, x_18);
x_20 = x_13;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
else
{
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMarkPersistent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitMarkPersistent(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_withErrRet(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__16));
x_5 = lean_string_append(x_3, x_4);
x_6 = lean_apply_2(x_1, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_22; 
x_7 = lean_ctor_get(x_6, 1);
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_6, 0);
lean_dec(x_23);
x_8 = x_6;
x_9 = x_22;
goto block_21;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__3));
x_11 = lean_string_append(x_7, x_10);
x_12 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_13 = lean_string_append(x_11, x_12);
x_14 = ((lean_object*)(l_Lean_IR_EmitC_withErrRet___closed__0));
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_box(0);
x_17 = lean_string_append(x_15, x_12);
if (x_9 == 0)
{
lean_ctor_set(x_8, 1, x_17);
lean_ctor_set(x_8, 0, x_16);
x_18 = x_8;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
else
{
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclInit___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitCName(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_17; 
x_5 = lean_ctor_get(x_4, 1);
x_17 = !lean_is_exclusive(x_4);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_4, 0);
lean_dec(x_18);
x_6 = x_4;
x_7 = x_17;
goto block_16;
}
else
{
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = ((lean_object*)(l_Lean_IR_EmitC_emitDeclInit___lam__0___closed__0));
x_9 = lean_string_append(x_5, x_8);
x_10 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_11 = lean_box(0);
x_12 = lean_string_append(x_9, x_10);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_12);
lean_ctor_set(x_6, 0, x_11);
x_13 = x_6;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclInit___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitCName(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_17; 
x_5 = lean_ctor_get(x_4, 1);
x_17 = !lean_is_exclusive(x_4);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_4, 0);
lean_dec(x_18);
x_6 = x_4;
x_7 = x_17;
goto block_16;
}
else
{
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = ((lean_object*)(l_Lean_IR_EmitC_emitDeclInit___lam__0___closed__0));
x_9 = lean_string_append(x_5, x_8);
x_10 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_11 = lean_box(0);
x_12 = lean_string_append(x_9, x_10);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_12);
lean_ctor_set(x_6, 0, x_11);
x_13 = x_6;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclInit(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_8; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_41; uint8_t x_55; uint8_t x_56; lean_object* x_61; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_17);
x_61 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitDeclInit___lam__1), 3, 1);
lean_closure_set(x_61, 0, x_17);
if (x_2 == 0)
{
goto block_87;
}
else
{
uint8_t x_88; 
lean_inc(x_17);
lean_inc_ref(x_16);
x_88 = l_Lean_isIOUnitBuiltinInitFn(x_16, x_17);
if (x_88 == 0)
{
goto block_87;
}
else
{
lean_dec(x_17);
goto block_77;
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
block_15:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__21));
x_10 = lean_string_append(x_8, x_9);
x_11 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_12 = lean_box(0);
x_13 = lean_string_append(x_10, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
block_40:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitDeclInit___lam__0), 3, 1);
lean_closure_set(x_19, 0, x_18);
lean_inc_ref(x_3);
x_20 = l_Lean_IR_EmitC_withErrRet(x_19, x_3, x_4);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_inc_ref(x_3);
lean_inc(x_17);
x_22 = l_Lean_IR_EmitC_emitCName(x_17, x_3, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l_Lean_IR_Decl_resultType(x_1);
x_25 = l_Lean_IR_IRType_isScalar(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_24);
x_26 = ((lean_object*)(l_Lean_IR_EmitC_emitDeclInit___closed__0));
x_27 = lean_string_append(x_23, x_26);
x_28 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lean_IR_EmitC_emitMarkPersistent(x_1, x_17, x_3, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec_ref(x_30);
x_8 = x_31;
goto block_15;
}
else
{
return x_30;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_17);
lean_dec_ref(x_3);
x_32 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__2));
x_33 = l_Lean_IR_getUnboxOpName(x_24);
lean_dec(x_24);
x_34 = lean_string_append(x_32, x_33);
lean_dec_ref(x_33);
x_35 = ((lean_object*)(l_Lean_IR_EmitC_emitDeclInit___closed__1));
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_string_append(x_23, x_36);
lean_dec_ref(x_36);
x_38 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_39 = lean_string_append(x_37, x_38);
x_8 = x_39;
goto block_15;
}
}
else
{
lean_dec(x_17);
lean_dec_ref(x_3);
return x_22;
}
}
else
{
lean_dec(x_17);
lean_dec_ref(x_3);
return x_20;
}
}
block_54:
{
if (x_41 == 0)
{
lean_dec(x_17);
lean_dec_ref(x_3);
goto block_7;
}
else
{
uint8_t x_42; 
lean_inc_ref(x_16);
x_42 = l_Lean_Compiler_LCNF_isSimpleGroundDecl(x_16, x_17);
if (x_42 == 0)
{
lean_object* x_43; 
lean_inc_ref(x_3);
lean_inc(x_17);
x_43 = l_Lean_IR_EmitC_emitCName(x_17, x_3, x_4);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = ((lean_object*)(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_mkAuxDecl___redArg___closed__2));
x_46 = lean_string_append(x_44, x_45);
lean_inc_ref(x_3);
lean_inc(x_17);
x_47 = l_Lean_IR_EmitC_emitCInitName(x_17, x_3, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = ((lean_object*)(l_Lean_IR_EmitC_emitDeclInit___closed__2));
x_50 = lean_string_append(x_48, x_49);
x_51 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_52 = lean_string_append(x_50, x_51);
x_53 = l_Lean_IR_EmitC_emitMarkPersistent(x_1, x_17, x_3, x_52);
return x_53;
}
else
{
lean_dec(x_17);
lean_dec_ref(x_3);
return x_47;
}
}
else
{
lean_dec(x_17);
lean_dec_ref(x_3);
return x_43;
}
}
else
{
lean_dec(x_17);
lean_dec_ref(x_3);
goto block_7;
}
}
}
block_60:
{
lean_object* x_57; 
lean_inc(x_17);
lean_inc_ref(x_16);
x_57 = lean_get_init_fn_name_for(x_16, x_17);
if (lean_obj_tag(x_57) == 1)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_18 = x_58;
goto block_40;
}
else
{
uint8_t x_59; 
lean_dec(x_57);
lean_inc_ref(x_16);
x_59 = l_Lean_isClosedTermName(x_16, x_17);
if (x_59 == 0)
{
x_41 = x_56;
goto block_54;
}
else
{
x_41 = x_55;
goto block_54;
}
}
}
block_77:
{
lean_object* x_62; 
x_62 = l_Lean_IR_EmitC_withErrRet(x_61, x_3, x_4);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_75; 
x_63 = lean_ctor_get(x_62, 1);
x_75 = !lean_is_exclusive(x_62);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_62, 0);
lean_dec(x_76);
x_64 = x_62;
x_65 = x_75;
goto block_74;
}
else
{
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_box(0);
x_65 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__21));
x_67 = lean_string_append(x_63, x_66);
x_68 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_69 = lean_box(0);
x_70 = lean_string_append(x_67, x_68);
if (x_65 == 0)
{
lean_ctor_set(x_64, 1, x_70);
lean_ctor_set(x_64, 0, x_69);
x_71 = x_64;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_70);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
}
else
{
return x_62;
}
}
block_87:
{
uint8_t x_78; 
lean_inc(x_17);
lean_inc_ref(x_16);
x_78 = l_Lean_isIOUnitInitFn(x_16, x_17);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_dec_ref(x_61);
x_79 = l_Lean_IR_Decl_params(x_1);
x_80 = lean_array_get_size(x_79);
lean_dec_ref(x_79);
x_81 = lean_unsigned_to_nat(0u);
x_82 = lean_nat_dec_eq(x_80, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_17);
lean_dec_ref(x_3);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_4);
return x_84;
}
else
{
if (x_2 == 0)
{
x_55 = x_78;
x_56 = x_82;
goto block_60;
}
else
{
lean_object* x_85; 
lean_inc(x_17);
lean_inc_ref(x_16);
x_85 = l_Lean_getBuiltinInitFnNameFor_x3f(x_16, x_17);
if (lean_obj_tag(x_85) == 0)
{
x_55 = x_78;
x_56 = x_82;
goto block_60;
}
else
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_18 = x_86;
goto block_40;
}
}
}
}
else
{
lean_dec(x_17);
goto block_77;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclInit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_IR_EmitC_emitDeclInit(x_1, x_5, x_3, x_4);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_IR_EmitC_emitInitFn_spec__1___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_16; uint8_t x_21; uint8_t x_24; uint8_t x_25; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_box(0);
x_24 = 2;
x_25 = l_Lean_instBEqIRPhases_beq(x_1, x_24);
if (x_25 == 0)
{
uint8_t x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; 
x_26 = 1;
x_27 = l_Lean_instBEqIRPhases_beq(x_1, x_26);
x_28 = l_Lean_IR_Decl_name(x_8);
lean_inc_ref(x_2);
x_29 = l_Lean_isMarkedMeta(x_2, x_28);
if (x_27 == 0)
{
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = 1;
x_16 = x_30;
goto block_20;
}
else
{
x_21 = x_27;
goto block_23;
}
}
else
{
x_21 = x_29;
goto block_23;
}
}
else
{
x_21 = x_25;
goto block_23;
}
block_15:
{
lean_object* x_12; 
lean_inc_ref(x_5);
x_12 = l_Lean_IR_EmitC_emitDeclInit(x_8, x_11, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
x_3 = x_9;
x_4 = x_10;
x_6 = x_13;
goto _start;
}
else
{
lean_dec_ref(x_5);
lean_dec_ref(x_2);
return x_12;
}
}
block_20:
{
uint8_t x_17; uint8_t x_18; 
x_17 = 1;
x_18 = l_Lean_instBEqIRPhases_beq(x_1, x_17);
if (x_18 == 0)
{
x_11 = x_16;
goto block_15;
}
else
{
uint8_t x_19; 
x_19 = 0;
x_11 = x_19;
goto block_15;
}
}
block_23:
{
if (x_21 == 0)
{
x_3 = x_9;
x_4 = x_10;
goto _start;
}
else
{
x_16 = x_21;
goto block_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_IR_EmitC_emitInitFn_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_List_forIn_x27_loop___at___00Lean_IR_EmitC_emitInitFn_spec__1___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_string_append(x_3, x_1);
x_5 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_6 = lean_box(0);
x_7 = lean_string_append(x_4, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_2, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_uget_borrowed(x_1, x_2);
x_15 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2___closed__0));
lean_inc(x_14);
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2___lam__0___boxed), 3, 1);
lean_closure_set(x_17, 0, x_16);
lean_inc_ref(x_5);
x_18 = l_Lean_IR_EmitC_withErrRet(x_17, x_5, x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__21));
x_21 = lean_string_append(x_19, x_20);
x_22 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_23 = lean_box(0);
x_24 = lean_string_append(x_21, x_22);
x_7 = x_23;
x_8 = x_24;
goto block_12;
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec_ref(x_18);
x_7 = x_25;
x_8 = x_26;
goto block_12;
}
else
{
lean_dec_ref(x_5);
return x_18;
}
}
}
else
{
lean_object* x_27; 
lean_dec_ref(x_5);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_6);
return x_27;
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_7;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_27; 
x_27 = lean_usize_dec_eq(x_4, x_5);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_40; uint8_t x_41; 
x_28 = lean_array_uget_borrowed(x_3, x_4);
x_40 = 2;
x_41 = l_Lean_instBEqIRPhases_beq(x_2, x_40);
if (x_41 == 0)
{
uint8_t x_42; uint8_t x_43; uint8_t x_44; 
x_42 = lean_ctor_get_uint8(x_28, sizeof(void*)*1 + 2);
x_43 = 1;
x_44 = l_Lean_instBEqIRPhases_beq(x_2, x_43);
if (x_42 == 0)
{
if (x_44 == 0)
{
goto block_39;
}
else
{
x_8 = x_6;
x_9 = x_7;
goto block_13;
}
}
else
{
if (x_44 == 0)
{
x_8 = x_6;
x_9 = x_7;
goto block_13;
}
else
{
goto block_39;
}
}
}
else
{
goto block_39;
}
block_39:
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
x_30 = lean_ctor_get_uint8(x_28, sizeof(void*)*1 + 2);
x_31 = l_Lean_Environment_getModuleIdx_x3f(x_1, x_29);
if (lean_obj_tag(x_31) == 1)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = l_Lean_Environment_getModulePackageByIdx_x3f(x_1, x_32);
lean_dec(x_32);
x_34 = 2;
x_35 = l_Lean_instBEqIRPhases_beq(x_2, x_34);
if (x_35 == 0)
{
if (x_30 == 0)
{
lean_inc(x_29);
x_14 = x_33;
x_15 = x_29;
x_16 = x_2;
goto block_26;
}
else
{
uint8_t x_36; 
x_36 = 0;
lean_inc(x_29);
x_14 = x_33;
x_15 = x_29;
x_16 = x_36;
goto block_26;
}
}
else
{
lean_inc(x_29);
x_14 = x_33;
x_15 = x_29;
x_16 = x_34;
goto block_26;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_31);
lean_dec_ref(x_6);
x_37 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0___redArg___closed__1));
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_7);
return x_38;
}
}
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_6);
lean_ctor_set(x_45, 1, x_7);
return x_45;
}
block_13:
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_4 = x_11;
x_6 = x_8;
x_7 = x_9;
goto _start;
}
block_26:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = l_Lean_mkModuleInitializationFunctionName(x_15, x_14, x_16);
lean_dec(x_14);
x_18 = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__0));
x_19 = lean_string_append(x_18, x_17);
x_20 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0___redArg___closed__0));
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_string_append(x_7, x_21);
lean_dec_ref(x_21);
x_23 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_array_push(x_6, x_17);
x_8 = x_25;
x_9 = x_24;
goto block_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_2);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0___redArg(x_1, x_8, x_3, x_9, x_10, x_6, x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = ((lean_object*)(l_Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0___closed__0));
x_9 = lean_nat_dec_lt(x_4, x_5);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_le(x_5, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_4, x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_usize_of_nat(x_4);
x_16 = lean_usize_of_nat(x_11);
x_17 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0___redArg(x_1, x_2, x_3, x_15, x_16, x_8, x_7);
return x_17;
}
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_usize_of_nat(x_4);
x_19 = lean_usize_of_nat(x_5);
x_20 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0___redArg(x_1, x_2, x_3, x_18, x_19, x_8, x_7);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInitFn(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Lean_Environment_imports(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get_size(x_6);
x_9 = l_Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0(x_4, x_1, x_6, x_7, x_8, x_2, x_3);
lean_dec_ref(x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_49; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
x_13 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = ((lean_object*)(l_Lean_IR_EmitC_emitInitFn___closed__0));
x_16 = l_Lean_mkModuleInitializationPrefix(x_1);
x_17 = lean_string_append(x_15, x_16);
lean_dec_ref(x_16);
x_18 = ((lean_object*)(l_Lean_IR_EmitC_emitInitFn___closed__1));
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_box(0);
x_21 = lean_box(0);
lean_inc_ref(x_4);
x_22 = l_Lean_PersistentEnvExtension_getState___redArg(x_20, x_12, x_4, x_14, x_21);
lean_dec(x_14);
lean_inc(x_5);
x_23 = l_Lean_mkModuleInitializationFunctionName(x_5, x_22, x_1);
lean_dec(x_22);
x_24 = ((lean_object*)(l_Lean_IR_EmitC_emitInitFn___closed__2));
x_25 = lean_string_append(x_24, x_19);
x_26 = ((lean_object*)(l_Lean_IR_EmitC_emitInitFn___closed__3));
x_27 = lean_string_append(x_25, x_26);
x_28 = ((lean_object*)(l_Lean_IR_EmitC_emitInitFn___closed__4));
x_29 = lean_string_append(x_28, x_23);
lean_dec_ref(x_23);
x_30 = ((lean_object*)(l_Lean_IR_EmitC_emitInitFn___closed__5));
x_31 = lean_string_append(x_29, x_30);
x_32 = ((lean_object*)(l_Lean_IR_EmitC_emitInitFn___closed__6));
x_33 = ((lean_object*)(l_Lean_IR_EmitC_emitIf___closed__0));
x_34 = lean_string_append(x_33, x_19);
x_35 = ((lean_object*)(l_Lean_IR_EmitC_emitInitFn___closed__7));
x_36 = lean_string_append(x_34, x_35);
x_37 = ((lean_object*)(l_Lean_IR_EmitC_emitInitFn___closed__8));
x_38 = lean_string_append(x_19, x_37);
x_39 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_38);
lean_ctor_set(x_52, 1, x_39);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_36);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_32);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_31);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_27);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_56, x_11);
lean_dec_ref(x_56);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = lean_array_get_size(x_10);
x_60 = lean_nat_dec_lt(x_7, x_59);
if (x_60 == 0)
{
lean_dec(x_10);
x_40 = x_58;
goto block_48;
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_box(0);
x_62 = lean_nat_dec_le(x_59, x_59);
if (x_62 == 0)
{
if (x_60 == 0)
{
lean_dec(x_10);
x_40 = x_58;
goto block_48;
}
else
{
size_t x_63; size_t x_64; lean_object* x_65; 
x_63 = 0;
x_64 = lean_usize_of_nat(x_59);
lean_inc_ref(x_2);
x_65 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2(x_10, x_63, x_64, x_61, x_2, x_58);
lean_dec(x_10);
x_49 = x_65;
goto block_51;
}
}
else
{
size_t x_66; size_t x_67; lean_object* x_68; 
x_66 = 0;
x_67 = lean_usize_of_nat(x_59);
lean_inc_ref(x_2);
x_68 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2(x_10, x_66, x_67, x_61, x_2, x_58);
lean_dec(x_10);
x_49 = x_68;
goto block_51;
}
}
block_48:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc_ref(x_4);
x_41 = l_Lean_IR_getDecls(x_4);
x_42 = l_List_reverse___redArg(x_41);
x_43 = lean_box(0);
x_44 = l_List_forIn_x27_loop___at___00Lean_IR_EmitC_emitInitFn_spec__1___redArg(x_1, x_4, x_42, x_43, x_2, x_40);
lean_dec(x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = ((lean_object*)(l_Lean_IR_EmitC_emitInitFn___closed__10));
x_47 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_46, x_45);
return x_47;
}
else
{
return x_44;
}
}
block_51:
{
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec_ref(x_49);
x_40 = x_50;
goto block_48;
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_49;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_77; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_69 = lean_ctor_get(x_9, 0);
x_70 = lean_ctor_get(x_9, 1);
x_77 = !lean_is_exclusive(x_9);
if (x_77 == 0)
{
x_71 = x_9;
x_72 = x_77;
goto block_76;
}
else
{
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_9);
x_71 = lean_box(0);
x_72 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_73; 
if (x_72 == 0)
{
x_73 = x_71;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_70);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInitFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_IR_EmitC_emitInitFn(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_IR_EmitC_emitInitFn_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___00Lean_IR_EmitC_emitInitFn_spec__1___redArg(x_1, x_2, x_4, x_5, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_IR_EmitC_emitInitFn_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_List_forIn_x27_loop___at___00Lean_IR_EmitC_emitInitFn_spec__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0(x_1, x_9, x_3, x_10, x_11, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLegacyInitFn___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2___closed__0));
x_5 = lean_string_append(x_1, x_4);
x_6 = lean_string_append(x_3, x_5);
lean_dec_ref(x_5);
x_7 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_8 = lean_box(0);
x_9 = lean_string_append(x_6, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLegacyInitFn___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitLegacyInitFn___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLegacyInitFn___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_9);
x_11 = l_Lean_PersistentEnvExtension_getState___redArg(x_1, x_2, x_9, x_3, x_4);
lean_inc(x_10);
x_12 = l_Lean_mkModuleInitializationFunctionName(x_10, x_11, x_5);
lean_dec(x_11);
x_13 = lean_apply_3(x_6, x_12, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLegacyInitFn___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
x_10 = l_Lean_IR_EmitC_emitLegacyInitFn___lam__1(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitLegacyInitFn_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_uget_borrowed(x_2, x_3);
x_9 = lean_ctor_get(x_8, 0);
x_10 = l_Lean_Environment_getModuleIdx_x3f(x_1, x_9);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_Environment_getModulePackageByIdx_x3f(x_1, x_11);
lean_dec(x_11);
x_13 = 2;
lean_inc(x_9);
x_14 = l_Lean_mkModuleInitializationFunctionName(x_9, x_12, x_13);
lean_dec(x_12);
x_15 = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_IR_EmitC_emitDeclAux_spec__0___redArg___closed__0));
x_16 = lean_string_append(x_15, x_14);
x_17 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0___redArg___closed__0));
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_6, x_18);
lean_dec_ref(x_18);
x_20 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_array_push(x_5, x_14);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_3 = x_24;
x_5 = x_22;
x_6 = x_21;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_10);
lean_dec_ref(x_5);
x_26 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0_spec__0___redArg___closed__1));
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_6);
return x_27;
}
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_6);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitLegacyInitFn_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitLegacyInitFn_spec__0_spec__0___redArg(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_IR_EmitC_emitLegacyInitFn_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = ((lean_object*)(l_Array_filterMapM___at___00Lean_IR_EmitC_emitInitFn_spec__0___closed__0));
x_8 = lean_nat_dec_lt(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_le(x_4, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_nat_dec_lt(x_3, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_usize_of_nat(x_3);
x_15 = lean_usize_of_nat(x_10);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitLegacyInitFn_spec__0_spec__0___redArg(x_1, x_2, x_14, x_15, x_7, x_6);
return x_16;
}
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_usize_of_nat(x_3);
x_18 = lean_usize_of_nat(x_4);
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitLegacyInitFn_spec__0_spec__0___redArg(x_1, x_2, x_17, x_18, x_7, x_6);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_IR_EmitC_emitLegacyInitFn_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_filterMapM___at___00Lean_IR_EmitC_emitLegacyInitFn_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLegacyInitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Environment_imports(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_5);
x_8 = l_Array_filterMapM___at___00Lean_IR_EmitC_emitLegacyInitFn_spec__0(x_3, x_5, x_6, x_7, x_1, x_2);
lean_dec_ref(x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_62; lean_object* x_65; uint8_t x_66; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = 2;
x_15 = lean_box(0);
x_16 = lean_box(0);
lean_inc_ref(x_3);
x_17 = l_Lean_PersistentEnvExtension_getState___redArg(x_15, x_11, x_3, x_13, x_16);
lean_inc(x_4);
x_18 = l_Lean_mkModuleInitializationFunctionName(x_4, x_17, x_14);
lean_dec(x_17);
x_19 = ((lean_object*)(l_Lean_IR_EmitC_emitLegacyInitFn___closed__0));
x_20 = ((lean_object*)(l_Lean_IR_EmitC_emitInitFn___closed__4));
x_21 = lean_string_append(x_20, x_18);
x_22 = ((lean_object*)(l_Lean_IR_EmitC_emitInitFn___closed__5));
x_23 = lean_string_append(x_21, x_22);
x_24 = ((lean_object*)(l_Lean_IR_EmitC_emitLegacyInitFn___closed__5));
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_26, x_10);
lean_dec_ref(x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = ((lean_object*)(l_Lean_IR_EmitC_emitLegacyInitFn___closed__6));
x_65 = lean_array_get_size(x_9);
x_66 = lean_nat_dec_lt(x_6, x_65);
if (x_66 == 0)
{
lean_dec(x_9);
x_30 = x_28;
goto block_61;
}
else
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_box(0);
x_68 = lean_nat_dec_le(x_65, x_65);
if (x_68 == 0)
{
if (x_66 == 0)
{
lean_dec(x_9);
x_30 = x_28;
goto block_61;
}
else
{
size_t x_69; size_t x_70; lean_object* x_71; 
x_69 = 0;
x_70 = lean_usize_of_nat(x_65);
lean_inc_ref(x_1);
x_71 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2(x_9, x_69, x_70, x_67, x_1, x_28);
lean_dec(x_9);
x_62 = x_71;
goto block_64;
}
}
else
{
size_t x_72; size_t x_73; lean_object* x_74; 
x_72 = 0;
x_73 = lean_usize_of_nat(x_65);
lean_inc_ref(x_1);
x_74 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_EmitC_emitInitFn_spec__2(x_9, x_72, x_73, x_67, x_1, x_28);
lean_dec(x_9);
x_62 = x_74;
goto block_64;
}
}
block_61:
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = 0;
x_32 = lean_box(x_31);
lean_inc(x_13);
x_33 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitLegacyInitFn___lam__1___boxed), 8, 6);
lean_closure_set(x_33, 0, x_15);
lean_closure_set(x_33, 1, x_11);
lean_closure_set(x_33, 2, x_13);
lean_closure_set(x_33, 3, x_16);
lean_closure_set(x_33, 4, x_32);
lean_closure_set(x_33, 5, x_29);
lean_inc_ref(x_1);
x_34 = l_Lean_IR_EmitC_withErrRet(x_33, x_1, x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__21));
x_37 = lean_string_append(x_35, x_36);
x_38 = ((lean_object*)(l_Lean_IR_EmitC_emitLn___redArg___closed__0));
x_39 = lean_string_append(x_37, x_38);
x_40 = 1;
x_41 = lean_box(x_40);
x_42 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitLegacyInitFn___lam__1___boxed), 8, 6);
lean_closure_set(x_42, 0, x_15);
lean_closure_set(x_42, 1, x_11);
lean_closure_set(x_42, 2, x_13);
lean_closure_set(x_42, 3, x_16);
lean_closure_set(x_42, 4, x_41);
lean_closure_set(x_42, 5, x_29);
x_43 = l_Lean_IR_EmitC_withErrRet(x_42, x_1, x_39);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_59; 
x_44 = lean_ctor_get(x_43, 1);
x_59 = !lean_is_exclusive(x_43);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_43, 0);
lean_dec(x_60);
x_45 = x_43;
x_46 = x_59;
goto block_58;
}
else
{
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_box(0);
x_46 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_string_append(x_44, x_36);
x_48 = lean_string_append(x_47, x_38);
x_49 = ((lean_object*)(l_Lean_IR_EmitC_emitBlock___closed__0));
x_50 = lean_string_append(x_49, x_18);
lean_dec_ref(x_18);
x_51 = ((lean_object*)(l_Lean_IR_EmitC_emitLegacyInitFn___closed__7));
x_52 = lean_string_append(x_50, x_51);
x_53 = ((lean_object*)(l_Lean_IR_EmitC_emitMainFn___closed__35));
if (x_46 == 0)
{
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 1, x_53);
lean_ctor_set(x_45, 0, x_52);
x_54 = x_45;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_53);
x_54 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_55; 
x_55 = l_List_forM___at___00Lean_IR_EmitC_emitLns___at___00Lean_IR_EmitC_emitMainFn_spec__0_spec__0___redArg(x_54, x_48);
lean_dec_ref(x_54);
return x_55;
}
}
}
else
{
lean_dec_ref(x_18);
return x_43;
}
}
else
{
lean_dec_ref(x_18);
lean_dec(x_13);
lean_dec_ref(x_1);
return x_34;
}
}
block_64:
{
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec_ref(x_62);
x_30 = x_63;
goto block_61;
}
else
{
lean_dec_ref(x_18);
lean_dec(x_13);
lean_dec_ref(x_1);
return x_62;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_83; 
lean_dec_ref(x_1);
x_75 = lean_ctor_get(x_8, 0);
x_76 = lean_ctor_get(x_8, 1);
x_83 = !lean_is_exclusive(x_8);
if (x_83 == 0)
{
x_77 = x_8;
x_78 = x_83;
goto block_82;
}
else
{
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_8);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_76);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitLegacyInitFn_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitLegacyInitFn_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitLegacyInitFn_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_EmitC_emitLegacyInitFn_spec__0_spec__0(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_9; 
lean_inc_ref(x_1);
x_9 = l_Lean_IR_EmitC_emitFileHeader(x_1, x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_inc_ref(x_1);
x_11 = l_Lean_IR_EmitC_emitFnDecls(x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc_ref(x_1);
x_13 = l_Lean_IR_EmitC_emitFns(x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_1, 0);
x_16 = l_Lean_Environment_header(x_15);
x_17 = lean_ctor_get_uint8(x_16, sizeof(void*)*7 + 4);
lean_dec_ref(x_16);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; 
x_18 = 2;
lean_inc_ref(x_1);
x_19 = l_Lean_IR_EmitC_emitInitFn(x_18, x_1, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec_ref(x_19);
x_3 = x_1;
x_4 = x_20;
goto block_8;
}
else
{
lean_dec_ref(x_1);
return x_19;
}
}
else
{
uint8_t x_21; lean_object* x_22; 
x_21 = 0;
lean_inc_ref(x_1);
x_22 = l_Lean_IR_EmitC_emitInitFn(x_21, x_1, x_14);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = 1;
lean_inc_ref(x_1);
x_25 = l_Lean_IR_EmitC_emitInitFn(x_24, x_1, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec_ref(x_25);
lean_inc_ref(x_1);
x_27 = l_Lean_IR_EmitC_emitLegacyInitFn(x_1, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec_ref(x_27);
x_3 = x_1;
x_4 = x_28;
goto block_8;
}
else
{
lean_dec_ref(x_1);
return x_27;
}
}
else
{
lean_dec_ref(x_1);
return x_25;
}
}
else
{
lean_dec_ref(x_1);
return x_22;
}
}
}
else
{
lean_dec_ref(x_1);
return x_13;
}
}
else
{
lean_dec_ref(x_1);
return x_11;
}
}
else
{
lean_dec_ref(x_1);
return x_9;
}
block_8:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitMainFnIfNeeded(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_IR_EmitC_emitFileFooter___redArg(x_6);
return x_7;
}
else
{
return x_5;
}
}
}
}
static lean_object* _init_l_Lean_IR_emitC___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_emitC___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_IR_emitC___closed__0, &l_Lean_IR_emitC___closed__0_once, _init_l_Lean_IR_emitC___closed__0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_emitC(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_obj_once(&l_Lean_IR_emitC___closed__1, &l_Lean_IR_emitC___closed__1_once, _init_l_Lean_IR_emitC___closed__1);
x_4 = lean_box(0);
x_5 = ((lean_object*)(l_Lean_IR_EmitC_emitFnDeclAux___closed__2));
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
x_7 = ((lean_object*)(l_panic___at___00Lean_IR_EmitC_toCType_spec__0___closed__0));
x_8 = l_Lean_IR_EmitC_main(x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
lean_object* runtime_initialize_Lean_Compiler_NameMangling(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_EmitUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_NormIds(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_SimpCase(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ModPkgExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ClosedTermCache(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_SimpleGroundExpr(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Lean_Runtime(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_EmitC(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_NameMangling(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_EmitUtil(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_NormIds(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_SimpCase(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ModPkgExt(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Types(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ClosedTermCache(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_SimpleGroundExpr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Runtime(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__3___boxed__const__1 = _init_l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__3___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_EmitC_0__Lean_IR_EmitC_emitGroundDecl_groundNameMkStrToCLit___closed__3___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_IR_EmitC(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_NameMangling(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_EmitUtil(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_NormIds(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_SimpCase(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ModPkgExt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Types(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ClosedTermCache(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_SimpleGroundExpr(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Lean_Runtime(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_EmitC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_NameMangling(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_EmitUtil(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_NormIds(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_SimpCase(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ModPkgExt(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Types(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ClosedTermCache(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_SimpleGroundExpr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Runtime(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_EmitC(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_IR_EmitC(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_IR_EmitC(builtin);
}
#ifdef __cplusplus
}
#endif
