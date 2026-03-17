// Lean compiler output
// Module: Lean.Compiler.Specialize
// Imports: public import Lean.Meta.Basic import Init.Omega
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedConfigWithKey___private__1;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___redArg(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_specialize_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_specialize_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_specialize_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_specialize_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_instInhabitedSpecializeAttributeKind_default;
LEAN_EXPORT uint8_t l_Lean_Compiler_instInhabitedSpecializeAttributeKind;
LEAN_EXPORT uint8_t l_Lean_Compiler_instBEqSpecializeAttributeKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_instBEqSpecializeAttributeKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_instBEqSpecializeAttributeKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_instBEqSpecializeAttributeKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_instBEqSpecializeAttributeKind___closed__0 = (const lean_object*)&l_Lean_Compiler_instBEqSpecializeAttributeKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_instBEqSpecializeAttributeKind = (const lean_object*)&l_Lean_Compiler_instBEqSpecializeAttributeKind___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nospecialize"};
static const lean_object* l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 38, 76, 194, 31, 149, 48, 135)}};
static const lean_object* l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "mark definition to never be specialized"};
static const lean_object* l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "nospecializeAttr"};
static const lean_object* l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 58, 232, 107, 183, 159, 132, 232)}};
static const lean_object* l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_nospecializeAttr;
static const lean_string_object l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "Marks a definition to never be specialized during code generation.\n"};
static const lean_object* l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1___closed__0 = (const lean_object*)&l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1();
LEAN_EXPORT lean_object* l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__0 = (const lean_object*)&l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(78) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__1 = (const lean_object*)&l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(78) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__2 = (const lean_object*)&l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__3 = (const lean_object*)&l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__4 = (const lean_object*)&l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__4_value),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__5 = (const lean_object*)&l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__2_value),((lean_object*)&l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__6 = (const lean_object*)&l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Invalid specialization argument index `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "`: The argument at this index (`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "`) has already been specified as a specialization candidate"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Invalid argument index `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "`: `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "` has only "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " arguments"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__12_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "Invalid specialization argument index `0`: Index must be greater than 0"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__14_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Invalid specialization argument name `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__16_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "`: It has already been specified as a specialization candidate"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__18_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "` does not have an argument with this name"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__20_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___closed__0 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_initFn___lam__1___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_initFn___lam__1___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
static const lean_array_object l_Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "specializeAttr"};
static const lean_object* l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 4, 174, 8, 190, 202, 8, 76)}};
static const lean_object* l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "specialize"};
static const lean_object* l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(241, 143, 174, 76, 41, 16, 248, 244)}};
static const lean_object* l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "mark definition to always be specialized"};
static const lean_object* l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttr;
static const lean_string_object l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 750, .m_capacity = 750, .m_length = 749, .m_data = "Marks a definition to always be specialized during code generation.\n\nSpecialization is an optimization in the code generator for generating variants of a function that\nare specialized to specific parameter values. This is in particular useful for functions that take\nother functions as parameters: Usually when passing functions as parameters, a closure needs to be\nallocated that will then be called. Using `@[specialize]` prevents both of these operations by\nusing the provided function directly in the specialization of the inner function.\n\n`@[specialize]` can take additional arguments for the parameter names or indices (starting at 1) of\nthe parameters that should be specialized. By default, instance and function parameters are\nspecialized.\n"};
static const lean_object* l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1___closed__0 = (const lean_object*)&l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1();
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(53) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__0 = (const lean_object*)&l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(74) << 1) | 1)),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__1 = (const lean_object*)&l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__2 = (const lean_object*)&l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(67) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__3 = (const lean_object*)&l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(67) << 1) | 1)),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__4 = (const lean_object*)&l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__4_value),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__5 = (const lean_object*)&l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__2_value),((lean_object*)&l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__6 = (const lean_object*)&l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___boxed(lean_object*);
static lean_once_cell_t l_Lean_Compiler_getSpecializationArgs_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_getSpecializationArgs_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_getSpecializationArgs_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_hasSpecializeAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_hasSpecializeAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_hasNospecializeAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_hasNospecializeAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorIdx(uint8_t v_x_1_){
_start:
{
if (v_x_1_ == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_boxed_5_; lean_object* v_res_6_; 
v_x_boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Compiler_SpecializeAttributeKind_ctorIdx(v_x_boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_toCtorIdx(uint8_t v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_Compiler_SpecializeAttributeKind_ctorIdx(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_toCtorIdx___boxed(lean_object* v_x_9_){
_start:
{
uint8_t v_x_4__boxed_10_; lean_object* v_res_11_; 
v_x_4__boxed_10_ = lean_unbox(v_x_9_);
v_res_11_ = l_Lean_Compiler_SpecializeAttributeKind_toCtorIdx(v_x_4__boxed_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorElim___redArg(lean_object* v_k_12_){
_start:
{
lean_inc(v_k_12_);
return v_k_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorElim___redArg___boxed(lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_Compiler_SpecializeAttributeKind_ctorElim___redArg(v_k_13_);
lean_dec(v_k_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, uint8_t v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_inc(v_k_19_);
return v_k_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
uint8_t v_t_boxed_25_; lean_object* v_res_26_; 
v_t_boxed_25_ = lean_unbox(v_t_22_);
v_res_26_ = l_Lean_Compiler_SpecializeAttributeKind_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_boxed_25_, v_h_23_, v_k_24_);
lean_dec(v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_specialize_elim___redArg(lean_object* v_specialize_27_){
_start:
{
lean_inc(v_specialize_27_);
return v_specialize_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_specialize_elim___redArg___boxed(lean_object* v_specialize_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Compiler_SpecializeAttributeKind_specialize_elim___redArg(v_specialize_28_);
lean_dec(v_specialize_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_specialize_elim(lean_object* v_motive_30_, uint8_t v_t_31_, lean_object* v_h_32_, lean_object* v_specialize_33_){
_start:
{
lean_inc(v_specialize_33_);
return v_specialize_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_specialize_elim___boxed(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_specialize_37_){
_start:
{
uint8_t v_t_boxed_38_; lean_object* v_res_39_; 
v_t_boxed_38_ = lean_unbox(v_t_35_);
v_res_39_ = l_Lean_Compiler_SpecializeAttributeKind_specialize_elim(v_motive_34_, v_t_boxed_38_, v_h_36_, v_specialize_37_);
lean_dec(v_specialize_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim___redArg(lean_object* v_nospecialize_40_){
_start:
{
lean_inc(v_nospecialize_40_);
return v_nospecialize_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim___redArg___boxed(lean_object* v_nospecialize_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim___redArg(v_nospecialize_41_);
lean_dec(v_nospecialize_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim(lean_object* v_motive_43_, uint8_t v_t_44_, lean_object* v_h_45_, lean_object* v_nospecialize_46_){
_start:
{
lean_inc(v_nospecialize_46_);
return v_nospecialize_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim___boxed(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_nospecialize_50_){
_start:
{
uint8_t v_t_boxed_51_; lean_object* v_res_52_; 
v_t_boxed_51_ = lean_unbox(v_t_48_);
v_res_52_ = l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim(v_motive_47_, v_t_boxed_51_, v_h_49_, v_nospecialize_50_);
lean_dec(v_nospecialize_50_);
return v_res_52_;
}
}
static uint8_t _init_l_Lean_Compiler_instInhabitedSpecializeAttributeKind_default(void){
_start:
{
uint8_t v___x_53_; 
v___x_53_ = 0;
return v___x_53_;
}
}
static uint8_t _init_l_Lean_Compiler_instInhabitedSpecializeAttributeKind(void){
_start:
{
uint8_t v___x_54_; 
v___x_54_ = 0;
return v___x_54_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_instBEqSpecializeAttributeKind_beq(uint8_t v_x_55_, uint8_t v_y_56_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_57_ = l_Lean_Compiler_SpecializeAttributeKind_ctorIdx(v_x_55_);
v___x_58_ = l_Lean_Compiler_SpecializeAttributeKind_ctorIdx(v_y_56_);
v___x_59_ = lean_nat_dec_eq(v___x_57_, v___x_58_);
lean_dec(v___x_58_);
lean_dec(v___x_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_instBEqSpecializeAttributeKind_beq___boxed(lean_object* v_x_60_, lean_object* v_y_61_){
_start:
{
uint8_t v_x_17__boxed_62_; uint8_t v_y_18__boxed_63_; uint8_t v_res_64_; lean_object* v_r_65_; 
v_x_17__boxed_62_ = lean_unbox(v_x_60_);
v_y_18__boxed_63_ = lean_unbox(v_y_61_);
v_res_64_ = l_Lean_Compiler_instBEqSpecializeAttributeKind_beq(v_x_17__boxed_62_, v_y_18__boxed_63_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_(lean_object* v_x_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_box(0);
v___x_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2____boxed(lean_object* v_x_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_(v_x_74_, v___y_75_, v___y_76_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec(v_x_74_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___f_92_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_93_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_94_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_95_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_96_ = 0;
v___x_97_ = lean_box(2);
v___x_98_ = l_Lean_registerTagAttribute(v___x_93_, v___x_94_, v___f_92_, v___x_95_, v___x_96_, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2____boxed(lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_();
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1(){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_104_ = ((lean_object*)(l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1___closed__0));
v___x_105_ = l_Lean_addBuiltinDocString(v___x_103_, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1___boxed(lean_object* v_a_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1();
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3(){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_134_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_135_ = ((lean_object*)(l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__6));
v___x_136_ = l_Lean_addBuiltinDeclarationRanges(v___x_134_, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___boxed(lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3();
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0(lean_object* v_k_139_, lean_object* v_b_140_, lean_object* v_c_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = lean_apply_7(v_k_139_, v_b_140_, v_c_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, lean_box(0));
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0___boxed(lean_object* v_k_148_, lean_object* v_b_149_, lean_object* v_c_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0(v_k_148_, v_b_149_, v_c_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(lean_object* v_type_157_, lean_object* v_k_158_, uint8_t v_cleanupAnnotations_159_, uint8_t v_whnfType_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v___f_166_; lean_object* v___x_167_; 
v___f_166_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_166_, 0, v_k_158_);
v___x_167_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_157_, v___f_166_, v_cleanupAnnotations_159_, v_whnfType_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_175_ == 0)
{
v___x_170_ = v___x_167_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_167_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
else
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
v_a_176_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_167_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_167_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___boxed(lean_object* v_type_184_, lean_object* v_k_185_, lean_object* v_cleanupAnnotations_186_, lean_object* v_whnfType_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_193_; uint8_t v_whnfType_boxed_194_; lean_object* v_res_195_; 
v_cleanupAnnotations_boxed_193_ = lean_unbox(v_cleanupAnnotations_186_);
v_whnfType_boxed_194_ = lean_unbox(v_whnfType_187_);
v_res_195_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(v_type_184_, v_k_185_, v_cleanupAnnotations_boxed_193_, v_whnfType_boxed_194_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7(lean_object* v_00_u03b1_196_, lean_object* v_type_197_, lean_object* v_k_198_, uint8_t v_cleanupAnnotations_199_, uint8_t v_whnfType_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(v_type_197_, v_k_198_, v_cleanupAnnotations_199_, v_whnfType_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___boxed(lean_object* v_00_u03b1_207_, lean_object* v_type_208_, lean_object* v_k_209_, lean_object* v_cleanupAnnotations_210_, lean_object* v_whnfType_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_217_; uint8_t v_whnfType_boxed_218_; lean_object* v_res_219_; 
v_cleanupAnnotations_boxed_217_ = lean_unbox(v_cleanupAnnotations_210_);
v_whnfType_boxed_218_ = lean_unbox(v_whnfType_211_);
v_res_219_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7(v_00_u03b1_207_, v_type_208_, v_k_209_, v_cleanupAnnotations_boxed_217_, v_whnfType_boxed_218_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(lean_object* v_as_221_, lean_object* v_lo_222_, lean_object* v_hi_223_){
_start:
{
uint8_t v___x_224_; 
v___x_224_ = lean_nat_dec_lt(v_lo_222_, v_hi_223_);
if (v___x_224_ == 0)
{
lean_dec(v_lo_222_);
return v_as_221_;
}
else
{
lean_object* v___f_225_; lean_object* v___x_226_; lean_object* v_fst_227_; lean_object* v_snd_228_; uint8_t v___x_229_; 
v___f_225_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg___closed__0));
lean_inc(v_lo_222_);
v___x_226_ = l_Array_qpartition___redArg(v_as_221_, v___f_225_, v_lo_222_, v_hi_223_);
v_fst_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_fst_227_);
v_snd_228_ = lean_ctor_get(v___x_226_, 1);
lean_inc(v_snd_228_);
lean_dec_ref(v___x_226_);
v___x_229_ = lean_nat_dec_le(v_hi_223_, v_fst_227_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(v_snd_228_, v_lo_222_, v_fst_227_);
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = lean_nat_add(v_fst_227_, v___x_231_);
lean_dec(v_fst_227_);
v_as_221_ = v___x_230_;
v_lo_222_ = v___x_232_;
goto _start;
}
else
{
lean_dec(v_fst_227_);
lean_dec(v_lo_222_);
return v_snd_228_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg___boxed(lean_object* v_as_234_, lean_object* v_lo_235_, lean_object* v_hi_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(v_as_234_, v_lo_235_, v_hi_236_);
lean_dec(v_hi_236_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg(size_t v_sz_238_, size_t v_i_239_, lean_object* v_bs_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
uint8_t v___x_245_; 
v___x_245_ = lean_usize_dec_lt(v_i_239_, v_sz_238_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; 
lean_dec_ref(v___y_241_);
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v_bs_240_);
return v___x_246_;
}
else
{
lean_object* v_v_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_v_247_ = lean_array_uget_borrowed(v_bs_240_, v_i_239_);
v___x_248_ = l_Lean_Expr_fvarId_x21(v_v_247_);
lean_inc_ref(v___y_241_);
v___x_249_ = l_Lean_FVarId_getUserName___redArg(v___x_248_, v___y_241_, v___y_242_, v___y_243_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_251_; lean_object* v_bs_x27_252_; size_t v___x_253_; size_t v___x_254_; lean_object* v___x_255_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_a_250_);
lean_dec_ref(v___x_249_);
v___x_251_ = lean_unsigned_to_nat(0u);
v_bs_x27_252_ = lean_array_uset(v_bs_240_, v_i_239_, v___x_251_);
v___x_253_ = ((size_t)1ULL);
v___x_254_ = lean_usize_add(v_i_239_, v___x_253_);
v___x_255_ = lean_array_uset(v_bs_x27_252_, v_i_239_, v_a_250_);
v_i_239_ = v___x_254_;
v_bs_240_ = v___x_255_;
goto _start;
}
else
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
lean_dec_ref(v___y_241_);
lean_dec_ref(v_bs_240_);
v_a_257_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_249_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_249_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg___boxed(lean_object* v_sz_265_, lean_object* v_i_266_, lean_object* v_bs_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
size_t v_sz_boxed_272_; size_t v_i_boxed_273_; lean_object* v_res_274_; 
v_sz_boxed_272_ = lean_unbox_usize(v_sz_265_);
lean_dec(v_sz_265_);
v_i_boxed_273_ = lean_unbox_usize(v_i_266_);
lean_dec(v_i_266_);
v_res_274_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg(v_sz_boxed_272_, v_i_boxed_273_, v_bs_267_, v___y_268_, v___y_269_, v___y_270_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
return v_res_274_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1(lean_object* v_a_275_, lean_object* v_as_276_, size_t v_i_277_, size_t v_stop_278_){
_start:
{
uint8_t v___x_279_; 
v___x_279_ = lean_usize_dec_eq(v_i_277_, v_stop_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_280_ = lean_array_uget_borrowed(v_as_276_, v_i_277_);
v___x_281_ = lean_nat_dec_eq(v_a_275_, v___x_280_);
if (v___x_281_ == 0)
{
size_t v___x_282_; size_t v___x_283_; 
v___x_282_ = ((size_t)1ULL);
v___x_283_ = lean_usize_add(v_i_277_, v___x_282_);
v_i_277_ = v___x_283_;
goto _start;
}
else
{
return v___x_281_;
}
}
else
{
uint8_t v___x_285_; 
v___x_285_ = 0;
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1___boxed(lean_object* v_a_286_, lean_object* v_as_287_, lean_object* v_i_288_, lean_object* v_stop_289_){
_start:
{
size_t v_i_boxed_290_; size_t v_stop_boxed_291_; uint8_t v_res_292_; lean_object* v_r_293_; 
v_i_boxed_290_ = lean_unbox_usize(v_i_288_);
lean_dec(v_i_288_);
v_stop_boxed_291_ = lean_unbox_usize(v_stop_289_);
lean_dec(v_stop_289_);
v_res_292_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1(v_a_286_, v_as_287_, v_i_boxed_290_, v_stop_boxed_291_);
lean_dec_ref(v_as_287_);
lean_dec(v_a_286_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1(lean_object* v_as_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = lean_array_get_size(v_as_294_);
v___x_298_ = lean_nat_dec_lt(v___x_296_, v___x_297_);
if (v___x_298_ == 0)
{
return v___x_298_;
}
else
{
if (v___x_298_ == 0)
{
return v___x_298_;
}
else
{
size_t v___x_299_; size_t v___x_300_; uint8_t v___x_301_; 
v___x_299_ = ((size_t)0ULL);
v___x_300_ = lean_usize_of_nat(v___x_297_);
v___x_301_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1(v_a_295_, v_as_294_, v___x_299_, v___x_300_);
return v___x_301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1___boxed(lean_object* v_as_302_, lean_object* v_a_303_){
_start:
{
uint8_t v_res_304_; lean_object* v_r_305_; 
v_res_304_ = l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1(v_as_302_, v_a_303_);
lean_dec(v_a_303_);
lean_dec_ref(v_as_302_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5_spec__8(lean_object* v_xs_306_, lean_object* v_v_307_, lean_object* v_i_308_){
_start:
{
lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_309_ = lean_array_get_size(v_xs_306_);
v___x_310_ = lean_nat_dec_lt(v_i_308_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; 
lean_dec(v_i_308_);
v___x_311_ = lean_box(0);
return v___x_311_;
}
else
{
lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_312_ = lean_array_fget_borrowed(v_xs_306_, v_i_308_);
v___x_313_ = lean_name_eq(v___x_312_, v_v_307_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_unsigned_to_nat(1u);
v___x_315_ = lean_nat_add(v_i_308_, v___x_314_);
lean_dec(v_i_308_);
v_i_308_ = v___x_315_;
goto _start;
}
else
{
lean_object* v___x_317_; 
v___x_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_317_, 0, v_i_308_);
return v___x_317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_318_, lean_object* v_v_319_, lean_object* v_i_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5_spec__8(v_xs_318_, v_v_319_, v_i_320_);
lean_dec(v_v_319_);
lean_dec_ref(v_xs_318_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5(lean_object* v_xs_322_, lean_object* v_v_323_){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5_spec__8(v_xs_322_, v_v_323_, v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5___boxed(lean_object* v_xs_326_, lean_object* v_v_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5(v_xs_326_, v_v_327_);
lean_dec(v_v_327_);
lean_dec_ref(v_xs_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3(lean_object* v_xs_329_, lean_object* v_v_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5(v_xs_329_, v_v_330_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v___x_332_; 
v___x_332_ = lean_box(0);
return v___x_332_;
}
else
{
lean_object* v_val_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
v_val_333_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_331_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_val_333_);
lean_dec(v___x_331_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_val_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3___boxed(lean_object* v_xs_341_, lean_object* v_v_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3(v_xs_341_, v_v_342_);
lean_dec(v_v_342_);
lean_dec_ref(v_xs_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5(lean_object* v_msgData_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v___x_350_; lean_object* v_env_351_; lean_object* v___x_352_; lean_object* v_mctx_353_; lean_object* v_lctx_354_; lean_object* v_options_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_350_ = lean_st_ref_get(v___y_348_);
v_env_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc_ref(v_env_351_);
lean_dec(v___x_350_);
v___x_352_ = lean_st_ref_get(v___y_346_);
v_mctx_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc_ref(v_mctx_353_);
lean_dec(v___x_352_);
v_lctx_354_ = lean_ctor_get(v___y_345_, 2);
v_options_355_ = lean_ctor_get(v___y_347_, 2);
lean_inc_ref(v_options_355_);
lean_inc_ref(v_lctx_354_);
v___x_356_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_356_, 0, v_env_351_);
lean_ctor_set(v___x_356_, 1, v_mctx_353_);
lean_ctor_set(v___x_356_, 2, v_lctx_354_);
lean_ctor_set(v___x_356_, 3, v_options_355_);
v___x_357_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v_msgData_344_);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5___boxed(lean_object* v_msgData_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5(v_msgData_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg(lean_object* v_msg_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_ref_372_; lean_object* v___x_373_; lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_382_; 
v_ref_372_ = lean_ctor_get(v___y_369_, 5);
v___x_373_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5(v_msg_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_382_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_380_; 
lean_inc(v_ref_372_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v_ref_372_);
lean_ctor_set(v___x_378_, 1, v_a_374_);
if (v_isShared_377_ == 0)
{
lean_ctor_set_tag(v___x_376_, 1);
lean_ctor_set(v___x_376_, 0, v___x_378_);
v___x_380_ = v___x_376_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg___boxed(lean_object* v_msg_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg(v_msg_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(lean_object* v_ref_390_, lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_fileName_397_; lean_object* v_fileMap_398_; lean_object* v_options_399_; lean_object* v_currRecDepth_400_; lean_object* v_maxRecDepth_401_; lean_object* v_ref_402_; lean_object* v_currNamespace_403_; lean_object* v_openDecls_404_; lean_object* v_initHeartbeats_405_; lean_object* v_maxHeartbeats_406_; lean_object* v_quotContext_407_; lean_object* v_currMacroScope_408_; uint8_t v_diag_409_; lean_object* v_cancelTk_x3f_410_; uint8_t v_suppressElabErrors_411_; lean_object* v_inheritedTraceOptions_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_421_; 
v_fileName_397_ = lean_ctor_get(v___y_394_, 0);
v_fileMap_398_ = lean_ctor_get(v___y_394_, 1);
v_options_399_ = lean_ctor_get(v___y_394_, 2);
v_currRecDepth_400_ = lean_ctor_get(v___y_394_, 3);
v_maxRecDepth_401_ = lean_ctor_get(v___y_394_, 4);
v_ref_402_ = lean_ctor_get(v___y_394_, 5);
v_currNamespace_403_ = lean_ctor_get(v___y_394_, 6);
v_openDecls_404_ = lean_ctor_get(v___y_394_, 7);
v_initHeartbeats_405_ = lean_ctor_get(v___y_394_, 8);
v_maxHeartbeats_406_ = lean_ctor_get(v___y_394_, 9);
v_quotContext_407_ = lean_ctor_get(v___y_394_, 10);
v_currMacroScope_408_ = lean_ctor_get(v___y_394_, 11);
v_diag_409_ = lean_ctor_get_uint8(v___y_394_, sizeof(void*)*14);
v_cancelTk_x3f_410_ = lean_ctor_get(v___y_394_, 12);
v_suppressElabErrors_411_ = lean_ctor_get_uint8(v___y_394_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_412_ = lean_ctor_get(v___y_394_, 13);
v_isSharedCheck_421_ = !lean_is_exclusive(v___y_394_);
if (v_isSharedCheck_421_ == 0)
{
v___x_414_ = v___y_394_;
v_isShared_415_ = v_isSharedCheck_421_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_inheritedTraceOptions_412_);
lean_inc(v_cancelTk_x3f_410_);
lean_inc(v_currMacroScope_408_);
lean_inc(v_quotContext_407_);
lean_inc(v_maxHeartbeats_406_);
lean_inc(v_initHeartbeats_405_);
lean_inc(v_openDecls_404_);
lean_inc(v_currNamespace_403_);
lean_inc(v_ref_402_);
lean_inc(v_maxRecDepth_401_);
lean_inc(v_currRecDepth_400_);
lean_inc(v_options_399_);
lean_inc(v_fileMap_398_);
lean_inc(v_fileName_397_);
lean_dec(v___y_394_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_421_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v_ref_416_; lean_object* v___x_418_; 
v_ref_416_ = l_Lean_replaceRef(v_ref_390_, v_ref_402_);
lean_dec(v_ref_402_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 5, v_ref_416_);
v___x_418_ = v___x_414_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_fileName_397_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_fileMap_398_);
lean_ctor_set(v_reuseFailAlloc_420_, 2, v_options_399_);
lean_ctor_set(v_reuseFailAlloc_420_, 3, v_currRecDepth_400_);
lean_ctor_set(v_reuseFailAlloc_420_, 4, v_maxRecDepth_401_);
lean_ctor_set(v_reuseFailAlloc_420_, 5, v_ref_416_);
lean_ctor_set(v_reuseFailAlloc_420_, 6, v_currNamespace_403_);
lean_ctor_set(v_reuseFailAlloc_420_, 7, v_openDecls_404_);
lean_ctor_set(v_reuseFailAlloc_420_, 8, v_initHeartbeats_405_);
lean_ctor_set(v_reuseFailAlloc_420_, 9, v_maxHeartbeats_406_);
lean_ctor_set(v_reuseFailAlloc_420_, 10, v_quotContext_407_);
lean_ctor_set(v_reuseFailAlloc_420_, 11, v_currMacroScope_408_);
lean_ctor_set(v_reuseFailAlloc_420_, 12, v_cancelTk_x3f_410_);
lean_ctor_set(v_reuseFailAlloc_420_, 13, v_inheritedTraceOptions_412_);
lean_ctor_set_uint8(v_reuseFailAlloc_420_, sizeof(void*)*14, v_diag_409_);
lean_ctor_set_uint8(v_reuseFailAlloc_420_, sizeof(void*)*14 + 1, v_suppressElabErrors_411_);
v___x_418_ = v_reuseFailAlloc_420_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg(v_msg_391_, v___y_392_, v___y_393_, v___x_418_, v___y_395_);
lean_dec_ref(v___x_418_);
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg___boxed(lean_object* v_ref_422_, lean_object* v_msg_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_ref_422_, v_msg_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v_ref_422_);
return v_res_429_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__0));
v___x_432_ = l_Lean_stringToMessageData(v___x_431_);
return v___x_432_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__2));
v___x_435_ = l_Lean_stringToMessageData(v___x_434_);
return v___x_435_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__4));
v___x_438_ = l_Lean_stringToMessageData(v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__6));
v___x_441_ = l_Lean_stringToMessageData(v___x_440_);
return v___x_441_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__8));
v___x_444_ = l_Lean_stringToMessageData(v___x_443_);
return v___x_444_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__10));
v___x_447_ = l_Lean_stringToMessageData(v___x_446_);
return v___x_447_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__12));
v___x_450_ = l_Lean_stringToMessageData(v___x_449_);
return v___x_450_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__14));
v___x_453_ = l_Lean_stringToMessageData(v___x_452_);
return v___x_453_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__16));
v___x_456_ = l_Lean_stringToMessageData(v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__18));
v___x_459_ = l_Lean_stringToMessageData(v___x_458_);
return v___x_459_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__20));
v___x_462_ = l_Lean_stringToMessageData(v___x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4(lean_object* v_a_463_, lean_object* v_declName_464_, lean_object* v___x_465_, lean_object* v_as_466_, size_t v_sz_467_, size_t v_i_468_, lean_object* v_b_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_a_476_; lean_object* v___y_481_; uint8_t v___x_483_; 
v___x_483_ = lean_usize_dec_lt(v_i_468_, v_sz_467_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
lean_dec_ref(v___y_472_);
lean_dec(v_declName_464_);
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v_b_469_);
return v___x_484_;
}
else
{
lean_object* v___x_485_; uint8_t v___x_486_; lean_object* v_a_487_; lean_object* v___x_488_; 
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = lean_nat_dec_eq(v___x_465_, v___x_485_);
v_a_487_ = lean_array_uget_borrowed(v_as_466_, v_i_468_);
v___x_488_ = l_Lean_Syntax_isNatLit_x3f(v_a_487_);
if (lean_obj_tag(v___x_488_) == 1)
{
lean_object* v_val_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_566_; 
v_val_489_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_566_ == 0)
{
v___x_491_ = v___x_488_;
v_isShared_492_ = v_isSharedCheck_566_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_val_489_);
lean_dec(v___x_488_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_566_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; uint8_t v___x_555_; 
v___x_555_ = lean_nat_dec_eq(v_val_489_, v___x_485_);
if (v___x_555_ == 0)
{
lean_inc_ref(v___y_472_);
v___y_494_ = v___y_470_;
v___y_495_ = v___y_471_;
v___y_496_ = v___y_472_;
v___y_497_ = v___y_473_;
goto v___jp_493_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15);
lean_inc_ref(v___y_472_);
v___x_557_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_487_, v___x_556_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_dec_ref(v___x_557_);
lean_inc_ref(v___y_472_);
v___y_494_ = v___y_470_;
v___y_495_ = v___y_471_;
v___y_496_ = v___y_472_;
v___y_497_ = v___y_473_;
goto v___jp_493_;
}
else
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
lean_del_object(v___x_491_);
lean_dec(v_val_489_);
lean_dec_ref(v___y_472_);
lean_dec_ref(v_b_469_);
lean_dec(v_declName_464_);
v_a_558_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v___x_557_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_557_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_a_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
v___jp_493_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_498_ = lean_unsigned_to_nat(1u);
v___x_499_ = lean_nat_sub(v_val_489_, v___x_498_);
lean_dec(v_val_489_);
v___x_500_ = lean_array_get_size(v_a_463_);
v___x_501_ = lean_nat_dec_le(v___x_500_, v___x_499_);
if (v___x_501_ == 0)
{
uint8_t v___x_502_; 
v___x_502_ = l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1(v_b_469_, v___x_499_);
if (v___x_502_ == 0)
{
lean_dec_ref(v___y_496_);
lean_del_object(v___x_491_);
v___y_481_ = v___x_499_;
goto v___jp_480_;
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_503_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1);
v___x_504_ = lean_nat_add(v___x_499_, v___x_498_);
v___x_505_ = l_Nat_reprFast(v___x_504_);
if (v_isShared_492_ == 0)
{
lean_ctor_set_tag(v___x_491_, 3);
lean_ctor_set(v___x_491_, 0, v___x_505_);
v___x_507_ = v___x_491_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_526_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_508_ = l_Lean_MessageData_ofFormat(v___x_507_);
v___x_509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_503_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v___x_510_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3);
v___x_511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_509_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v___x_512_ = lean_array_fget_borrowed(v_a_463_, v___x_499_);
lean_inc(v___x_512_);
v___x_513_ = l_Lean_MessageData_ofName(v___x_512_);
v___x_514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_511_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___x_515_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5);
v___x_516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_487_, v___x_516_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_dec_ref(v___x_517_);
v___y_481_ = v___x_499_;
goto v___jp_480_;
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec(v___x_499_);
lean_dec_ref(v___y_472_);
lean_dec_ref(v_b_469_);
lean_dec(v_declName_464_);
v_a_518_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_517_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_527_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7);
v___x_528_ = l_Nat_reprFast(v___x_499_);
if (v_isShared_492_ == 0)
{
lean_ctor_set_tag(v___x_491_, 3);
lean_ctor_set(v___x_491_, 0, v___x_528_);
v___x_530_ = v___x_491_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_528_);
v___x_530_ = v_reuseFailAlloc_554_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_531_ = l_Lean_MessageData_ofFormat(v___x_530_);
v___x_532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_527_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9);
v___x_534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
lean_inc(v_declName_464_);
v___x_535_ = l_Lean_MessageData_ofConstName(v_declName_464_, v___x_486_);
v___x_536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11);
v___x_538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = l_Nat_reprFast(v___x_500_);
v___x_540_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
v___x_541_ = l_Lean_MessageData_ofFormat(v___x_540_);
v___x_542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_538_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v___x_543_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13);
v___x_544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_487_, v___x_544_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_dec_ref(v___x_545_);
v_a_476_ = v_b_469_;
goto v___jp_475_;
}
else
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
lean_dec_ref(v___y_472_);
lean_dec_ref(v_b_469_);
lean_dec(v_declName_464_);
v_a_546_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_545_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_545_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
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
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec(v___x_488_);
v___x_567_ = l_Lean_Syntax_getId(v_a_487_);
v___x_568_ = l_Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3(v_a_463_, v___x_567_);
if (lean_obj_tag(v___x_568_) == 1)
{
lean_object* v_val_569_; uint8_t v___x_572_; 
v_val_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_val_569_);
lean_dec_ref(v___x_568_);
v___x_572_ = l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1(v_b_469_, v_val_569_);
if (v___x_572_ == 0)
{
lean_dec(v___x_567_);
goto v___jp_570_;
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_573_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17);
v___x_574_ = l_Lean_MessageData_ofName(v___x_567_);
v___x_575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_573_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19);
v___x_577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
lean_inc_ref(v___y_472_);
v___x_578_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_487_, v___x_577_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_dec_ref(v___x_578_);
goto v___jp_570_;
}
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_dec(v_val_569_);
lean_dec_ref(v___y_472_);
lean_dec_ref(v_b_469_);
lean_dec(v_declName_464_);
v_a_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
v___jp_570_:
{
lean_object* v___x_571_; 
v___x_571_ = lean_array_push(v_b_469_, v_val_569_);
v_a_476_ = v___x_571_;
goto v___jp_475_;
}
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
lean_dec(v___x_568_);
v___x_587_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17);
v___x_588_ = l_Lean_MessageData_ofName(v___x_567_);
v___x_589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_587_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9);
v___x_591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_589_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
lean_inc(v_declName_464_);
v___x_592_ = l_Lean_MessageData_ofConstName(v_declName_464_, v___x_486_);
v___x_593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_591_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21);
v___x_595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_593_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
lean_inc_ref(v___y_472_);
v___x_596_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_487_, v___x_595_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_dec_ref(v___x_596_);
v_a_476_ = v_b_469_;
goto v___jp_475_;
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_dec_ref(v___y_472_);
lean_dec_ref(v_b_469_);
lean_dec(v_declName_464_);
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
}
v___jp_475_:
{
size_t v___x_477_; size_t v___x_478_; 
v___x_477_ = ((size_t)1ULL);
v___x_478_ = lean_usize_add(v_i_468_, v___x_477_);
v_i_468_ = v___x_478_;
v_b_469_ = v_a_476_;
goto _start;
}
v___jp_480_:
{
lean_object* v___x_482_; 
v___x_482_ = lean_array_push(v_b_469_, v___y_481_);
v_a_476_ = v___x_482_;
goto v___jp_475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___boxed(lean_object* v_a_605_, lean_object* v_declName_606_, lean_object* v___x_607_, lean_object* v_as_608_, lean_object* v_sz_609_, lean_object* v_i_610_, lean_object* v_b_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
size_t v_sz_boxed_617_; size_t v_i_boxed_618_; lean_object* v_res_619_; 
v_sz_boxed_617_ = lean_unbox_usize(v_sz_609_);
lean_dec(v_sz_609_);
v_i_boxed_618_ = lean_unbox_usize(v_i_610_);
lean_dec(v_i_610_);
v_res_619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4(v_a_605_, v_declName_606_, v___x_607_, v_as_608_, v_sz_boxed_617_, v_i_boxed_618_, v_b_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec_ref(v_as_608_);
lean_dec(v___x_607_);
lean_dec_ref(v_a_605_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0(lean_object* v___x_620_, lean_object* v_args_621_, lean_object* v_declName_622_, lean_object* v___x_623_, lean_object* v_xs_624_, lean_object* v_x_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
size_t v_sz_631_; size_t v___x_632_; lean_object* v___x_633_; 
v_sz_631_ = lean_array_size(v_xs_624_);
v___x_632_ = ((size_t)0ULL);
lean_inc_ref(v___y_626_);
v___x_633_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg(v_sz_631_, v___x_632_, v_xs_624_, v___y_626_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_657_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_657_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_657_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_657_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; size_t v_sz_639_; lean_object* v___x_640_; 
v___x_638_ = lean_mk_empty_array_with_capacity(v___x_620_);
v_sz_639_ = lean_array_size(v_args_621_);
v___x_640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4(v_a_634_, v_declName_622_, v___x_623_, v_args_621_, v_sz_639_, v___x_632_, v___x_638_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
lean_dec_ref(v___y_626_);
lean_dec(v_a_634_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___x_649_; uint8_t v___x_650_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
v___x_649_ = lean_array_get_size(v_a_641_);
v___x_650_ = lean_nat_dec_eq(v___x_649_, v___x_620_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___y_654_; uint8_t v___x_656_; 
lean_dec_ref(v___x_640_);
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = lean_nat_sub(v___x_649_, v___x_651_);
v___x_656_ = lean_nat_dec_le(v___x_620_, v___x_652_);
if (v___x_656_ == 0)
{
lean_dec(v___x_620_);
lean_inc(v___x_652_);
v___y_654_ = v___x_652_;
goto v___jp_653_;
}
else
{
v___y_654_ = v___x_620_;
goto v___jp_653_;
}
v___jp_653_:
{
uint8_t v___x_655_; 
v___x_655_ = lean_nat_dec_le(v___y_654_, v___x_652_);
if (v___x_655_ == 0)
{
lean_dec(v___x_652_);
lean_inc(v___y_654_);
v___y_643_ = v___y_654_;
v___y_644_ = v___y_654_;
goto v___jp_642_;
}
else
{
v___y_643_ = v___y_654_;
v___y_644_ = v___x_652_;
goto v___jp_642_;
}
}
}
else
{
lean_dec(v_a_641_);
lean_del_object(v___x_636_);
lean_dec(v___x_620_);
return v___x_640_;
}
v___jp_642_:
{
lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_645_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(v_a_641_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_645_);
v___x_647_ = v___x_636_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
else
{
lean_del_object(v___x_636_);
lean_dec(v___x_620_);
return v___x_640_;
}
}
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref(v___y_628_);
lean_dec_ref(v___y_626_);
lean_dec(v_declName_622_);
lean_dec(v___x_620_);
v_a_658_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_633_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_633_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0___boxed(lean_object* v___x_666_, lean_object* v_args_667_, lean_object* v_declName_668_, lean_object* v___x_669_, lean_object* v_xs_670_, lean_object* v_x_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0(v___x_666_, v_args_667_, v_declName_668_, v___x_669_, v_xs_670_, v_x_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec(v___y_673_);
lean_dec_ref(v_x_671_);
lean_dec(v___x_669_);
lean_dec_ref(v_args_667_);
return v_res_677_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_678_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__0);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__2(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__1);
v___x_682_ = lean_unsigned_to_nat(0u);
v___x_683_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
lean_ctor_set(v___x_683_, 2, v___x_682_);
lean_ctor_set(v___x_683_, 3, v___x_681_);
lean_ctor_set(v___x_683_, 4, v___x_681_);
lean_ctor_set(v___x_683_, 5, v___x_681_);
lean_ctor_set(v___x_683_, 6, v___x_681_);
lean_ctor_set(v___x_683_, 7, v___x_681_);
lean_ctor_set(v___x_683_, 8, v___x_681_);
return v___x_683_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_684_ = lean_unsigned_to_nat(32u);
v___x_685_ = lean_mk_empty_array_with_capacity(v___x_684_);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
return v___x_686_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__4(void){
_start:
{
size_t v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_687_ = ((size_t)5ULL);
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_unsigned_to_nat(32u);
v___x_690_ = lean_mk_empty_array_with_capacity(v___x_689_);
v___x_691_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__3);
v___x_692_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v___x_690_);
lean_ctor_set(v___x_692_, 2, v___x_688_);
lean_ctor_set(v___x_692_, 3, v___x_688_);
lean_ctor_set_usize(v___x_692_, 4, v___x_687_);
return v___x_692_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_693_ = lean_box(1);
v___x_694_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__4);
v___x_695_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__1);
v___x_696_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v___x_694_);
lean_ctor_set(v___x_696_, 2, v___x_693_);
return v___x_696_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__7(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__6));
v___x_699_ = l_Lean_stringToMessageData(v___x_698_);
return v___x_699_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__9(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__8));
v___x_702_ = l_Lean_stringToMessageData(v___x_701_);
return v___x_702_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__11(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__10));
v___x_705_ = l_Lean_stringToMessageData(v___x_704_);
return v___x_705_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__13(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__12));
v___x_708_ = l_Lean_stringToMessageData(v___x_707_);
return v___x_708_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__15(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__14));
v___x_711_ = l_Lean_stringToMessageData(v___x_710_);
return v___x_711_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__17(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__16));
v___x_714_ = l_Lean_stringToMessageData(v___x_713_);
return v___x_714_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__19(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__18));
v___x_717_ = l_Lean_stringToMessageData(v___x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg(lean_object* v_msg_718_, lean_object* v_declHint_719_, lean_object* v___y_720_){
_start:
{
lean_object* v___x_722_; lean_object* v_env_723_; uint8_t v___x_724_; 
v___x_722_ = lean_st_ref_get(v___y_720_);
v_env_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc_ref(v_env_723_);
lean_dec(v___x_722_);
v___x_724_ = l_Lean_Name_isAnonymous(v_declHint_719_);
if (v___x_724_ == 0)
{
uint8_t v_isExporting_725_; 
v_isExporting_725_ = lean_ctor_get_uint8(v_env_723_, sizeof(void*)*8);
if (v_isExporting_725_ == 0)
{
lean_object* v___x_726_; 
lean_dec_ref(v_env_723_);
lean_dec(v_declHint_719_);
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v_msg_718_);
return v___x_726_;
}
else
{
lean_object* v___x_727_; uint8_t v___x_728_; 
lean_inc_ref(v_env_723_);
v___x_727_ = l_Lean_Environment_setExporting(v_env_723_, v___x_724_);
lean_inc(v_declHint_719_);
lean_inc_ref(v___x_727_);
v___x_728_ = l_Lean_Environment_contains(v___x_727_, v_declHint_719_, v_isExporting_725_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; 
lean_dec_ref(v___x_727_);
lean_dec_ref(v_env_723_);
lean_dec(v_declHint_719_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v_msg_718_);
return v___x_729_;
}
else
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v_c_735_; lean_object* v___x_736_; 
v___x_730_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__2);
v___x_731_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__5);
v___x_732_ = l_Lean_Options_empty;
v___x_733_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_733_, 0, v___x_727_);
lean_ctor_set(v___x_733_, 1, v___x_730_);
lean_ctor_set(v___x_733_, 2, v___x_731_);
lean_ctor_set(v___x_733_, 3, v___x_732_);
lean_inc(v_declHint_719_);
v___x_734_ = l_Lean_MessageData_ofConstName(v_declHint_719_, v___x_724_);
v_c_735_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_735_, 0, v___x_733_);
lean_ctor_set(v_c_735_, 1, v___x_734_);
v___x_736_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_723_, v_declHint_719_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
lean_dec_ref(v_env_723_);
lean_dec(v_declHint_719_);
v___x_737_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__7);
v___x_738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
lean_ctor_set(v___x_738_, 1, v_c_735_);
v___x_739_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__9);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_738_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = l_Lean_MessageData_note(v___x_740_);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v_msg_718_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
return v___x_743_;
}
else
{
lean_object* v_val_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_779_; 
v_val_744_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_779_ == 0)
{
v___x_746_ = v___x_736_;
v_isShared_747_ = v_isSharedCheck_779_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_val_744_);
lean_dec(v___x_736_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_779_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v_mod_751_; uint8_t v___x_752_; 
v___x_748_ = lean_box(0);
v___x_749_ = l_Lean_Environment_header(v_env_723_);
lean_dec_ref(v_env_723_);
v___x_750_ = l_Lean_EnvironmentHeader_moduleNames(v___x_749_);
v_mod_751_ = lean_array_get(v___x_748_, v___x_750_, v_val_744_);
lean_dec(v_val_744_);
lean_dec_ref(v___x_750_);
v___x_752_ = l_Lean_isPrivateName(v_declHint_719_);
lean_dec(v_declHint_719_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_753_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__11);
v___x_754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v_c_735_);
v___x_755_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__13);
v___x_756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_754_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = l_Lean_MessageData_ofName(v_mod_751_);
v___x_758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_756_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__15);
v___x_760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_758_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = l_Lean_MessageData_note(v___x_760_);
v___x_762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_762_, 0, v_msg_718_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
if (v_isShared_747_ == 0)
{
lean_ctor_set_tag(v___x_746_, 0);
lean_ctor_set(v___x_746_, 0, v___x_762_);
v___x_764_ = v___x_746_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_766_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__7);
v___x_767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v_c_735_);
v___x_768_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__17);
v___x_769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = l_Lean_MessageData_ofName(v_mod_751_);
v___x_771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_769_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__19);
v___x_773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_771_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = l_Lean_MessageData_note(v___x_773_);
v___x_775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_775_, 0, v_msg_718_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
if (v_isShared_747_ == 0)
{
lean_ctor_set_tag(v___x_746_, 0);
lean_ctor_set(v___x_746_, 0, v___x_775_);
v___x_777_ = v___x_746_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_780_; 
lean_dec_ref(v_env_723_);
lean_dec(v_declHint_719_);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v_msg_718_);
return v___x_780_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___boxed(lean_object* v_msg_781_, lean_object* v_declHint_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg(v_msg_781_, v_declHint_782_, v___y_783_);
lean_dec(v___y_783_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15(lean_object* v_msg_786_, lean_object* v_declHint_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___x_793_; lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_803_; 
v___x_793_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg(v_msg_786_, v_declHint_787_, v___y_791_);
v_a_794_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_803_ == 0)
{
v___x_796_ = v___x_793_;
v_isShared_797_ = v_isSharedCheck_803_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_793_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_803_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_801_; 
v___x_798_ = l_Lean_unknownIdentifierMessageTag;
v___x_799_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
lean_ctor_set(v___x_799_, 1, v_a_794_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_799_);
v___x_801_ = v___x_796_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_799_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15___boxed(lean_object* v_msg_804_, lean_object* v_declHint_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15(v_msg_804_, v_declHint_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14___redArg(lean_object* v_ref_812_, lean_object* v_msg_813_, lean_object* v_declHint_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v___x_820_; lean_object* v_a_821_; lean_object* v___x_822_; 
v___x_820_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15(v_msg_813_, v_declHint_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
lean_dec_ref(v___x_820_);
v___x_822_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_ref_812_, v_a_821_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14___redArg___boxed(lean_object* v_ref_823_, lean_object* v_msg_824_, lean_object* v_declHint_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14___redArg(v_ref_823_, v_msg_824_, v_declHint_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
lean_dec(v___y_829_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v_ref_823_);
return v_res_831_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg___closed__0));
v___x_834_ = l_Lean_stringToMessageData(v___x_833_);
return v___x_834_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg___closed__2));
v___x_837_ = l_Lean_stringToMessageData(v___x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg(lean_object* v_ref_838_, lean_object* v_constName_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v___x_845_; uint8_t v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_845_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg___closed__1);
v___x_846_ = 0;
lean_inc(v_constName_839_);
v___x_847_ = l_Lean_MessageData_ofConstName(v_constName_839_, v___x_846_);
v___x_848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_845_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg___closed__3);
v___x_850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14___redArg(v_ref_838_, v___x_850_, v_constName_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg___boxed(lean_object* v_ref_852_, lean_object* v_constName_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg(v_ref_852_, v_constName_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v_ref_852_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9___redArg(lean_object* v_constName_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_ref_866_; lean_object* v___x_867_; 
v_ref_866_ = lean_ctor_get(v___y_863_, 5);
lean_inc(v_ref_866_);
v___x_867_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg(v_ref_866_, v_constName_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v_ref_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9___redArg___boxed(lean_object* v_constName_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9___redArg(v_constName_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6(lean_object* v_constName_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v___x_881_; lean_object* v_env_882_; uint8_t v___x_883_; lean_object* v___x_884_; 
v___x_881_ = lean_st_ref_get(v___y_879_);
v_env_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc_ref(v_env_882_);
lean_dec(v___x_881_);
v___x_883_ = 0;
lean_inc(v_constName_875_);
v___x_884_ = l_Lean_Environment_find_x3f(v_env_882_, v_constName_875_, v___x_883_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9___redArg(v_constName_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
return v___x_885_;
}
else
{
lean_object* v_val_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec_ref(v___y_878_);
lean_dec(v_constName_875_);
v_val_886_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_884_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_val_886_);
lean_dec(v___x_884_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
lean_ctor_set_tag(v___x_888_, 0);
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_val_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6___boxed(lean_object* v_constName_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6(v_constName_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs(lean_object* v_declName_903_, lean_object* v_args_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; 
v___x_910_ = lean_array_get_size(v_args_904_);
v___x_911_ = lean_unsigned_to_nat(0u);
v___x_912_ = lean_nat_dec_eq(v___x_910_, v___x_911_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; 
lean_inc_ref(v_a_907_);
lean_inc(v_declName_903_);
v___x_913_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6(v_declName_903_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___f_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref(v___x_913_);
v___f_915_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0___boxed), 11, 4);
lean_closure_set(v___f_915_, 0, v___x_911_);
lean_closure_set(v___f_915_, 1, v_args_904_);
lean_closure_set(v___f_915_, 2, v_declName_903_);
lean_closure_set(v___f_915_, 3, v___x_910_);
v___x_916_ = l_Lean_ConstantInfo_type(v_a_914_);
lean_dec(v_a_914_);
v___x_917_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(v___x_916_, v___f_915_, v___x_912_, v___x_912_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
return v___x_917_;
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec_ref(v_args_904_);
lean_dec(v_declName_903_);
v_a_918_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_913_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_913_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
else
{
lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec_ref(v_args_904_);
lean_dec(v_declName_903_);
v___x_926_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___closed__0));
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
return v___x_927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___boxed(lean_object* v_declName_928_, lean_object* v_args_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs(v_declName_928_, v_args_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0(size_t v_sz_936_, size_t v_i_937_, lean_object* v_bs_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg(v_sz_936_, v_i_937_, v_bs_938_, v___y_939_, v___y_941_, v___y_942_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___boxed(lean_object* v_sz_945_, lean_object* v_i_946_, lean_object* v_bs_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
size_t v_sz_boxed_953_; size_t v_i_boxed_954_; lean_object* v_res_955_; 
v_sz_boxed_953_ = lean_unbox_usize(v_sz_945_);
lean_dec(v_sz_945_);
v_i_boxed_954_ = lean_unbox_usize(v_i_946_);
lean_dec(v_i_946_);
v_res_955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0(v_sz_boxed_953_, v_i_boxed_954_, v_bs_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2(lean_object* v_00_u03b1_956_, lean_object* v_ref_957_, lean_object* v_msg_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_ref_957_, v_msg_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___boxed(lean_object* v_00_u03b1_965_, lean_object* v_ref_966_, lean_object* v_msg_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2(v_00_u03b1_965_, v_ref_966_, v_msg_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v_ref_966_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5(lean_object* v_n_974_, lean_object* v_as_975_, lean_object* v_lo_976_, lean_object* v_hi_977_, lean_object* v_w_978_, lean_object* v_hlo_979_, lean_object* v_hhi_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(v_as_975_, v_lo_976_, v_hi_977_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___boxed(lean_object* v_n_982_, lean_object* v_as_983_, lean_object* v_lo_984_, lean_object* v_hi_985_, lean_object* v_w_986_, lean_object* v_hlo_987_, lean_object* v_hhi_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5(v_n_982_, v_as_983_, v_lo_984_, v_hi_985_, v_w_986_, v_hlo_987_, v_hhi_988_);
lean_dec(v_hi_985_);
lean_dec(v_n_982_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3(lean_object* v_00_u03b1_990_, lean_object* v_msg_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg(v_msg_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___boxed(lean_object* v_00_u03b1_998_, lean_object* v_msg_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3(v_00_u03b1_998_, v_msg_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9(lean_object* v_00_u03b1_1006_, lean_object* v_constName_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9___redArg(v_constName_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9___boxed(lean_object* v_00_u03b1_1014_, lean_object* v_constName_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9(v_00_u03b1_1014_, v_constName_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13(lean_object* v_00_u03b1_1022_, lean_object* v_ref_1023_, lean_object* v_constName_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___redArg(v_ref_1023_, v_constName_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13___boxed(lean_object* v_00_u03b1_1031_, lean_object* v_ref_1032_, lean_object* v_constName_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13(v_00_u03b1_1031_, v_ref_1032_, v_constName_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
lean_dec(v___y_1037_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v_ref_1032_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14(lean_object* v_00_u03b1_1040_, lean_object* v_ref_1041_, lean_object* v_msg_1042_, lean_object* v_declHint_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14___redArg(v_ref_1041_, v_msg_1042_, v_declHint_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14___boxed(lean_object* v_00_u03b1_1050_, lean_object* v_ref_1051_, lean_object* v_msg_1052_, lean_object* v_declHint_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14(v_00_u03b1_1050_, v_ref_1051_, v_msg_1052_, v_declHint_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v_ref_1051_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16(lean_object* v_msg_1060_, lean_object* v_declHint_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg(v_msg_1060_, v_declHint_1061_, v___y_1065_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___boxed(lean_object* v_msg_1068_, lean_object* v_declHint_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16(v_msg_1068_, v_declHint_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(lean_object* v_x_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = lean_box(0);
v___x_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object* v_x_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(v_x_1083_, v_x_1084_, v_x_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v_x_1085_);
lean_dec_ref(v_x_1084_);
lean_dec(v_x_1083_);
return v_res_1088_;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___lam__1___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_obj_once(&l_Lean_Compiler_initFn___lam__1___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l_Lean_Compiler_initFn___lam__1___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l_Lean_Compiler_initFn___lam__1___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
return v___x_1091_;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1092_ = lean_box(1);
v___x_1093_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__4);
v___x_1094_ = lean_obj_once(&l_Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l_Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l_Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1095_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
lean_ctor_set(v___x_1095_, 1, v___x_1093_);
lean_ctor_set(v___x_1095_, 2, v___x_1092_);
return v___x_1095_;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1098_ = lean_obj_once(&l_Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l_Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l_Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1099_ = lean_unsigned_to_nat(0u);
v___x_1100_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
lean_ctor_set(v___x_1100_, 2, v___x_1099_);
lean_ctor_set(v___x_1100_, 3, v___x_1098_);
lean_ctor_set(v___x_1100_, 4, v___x_1098_);
lean_ctor_set(v___x_1100_, 5, v___x_1098_);
lean_ctor_set(v___x_1100_, 6, v___x_1098_);
lean_ctor_set(v___x_1100_, 7, v___x_1098_);
lean_ctor_set(v___x_1100_, 8, v___x_1098_);
return v___x_1100_;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_obj_once(&l_Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l_Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l_Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1102_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
lean_ctor_set(v___x_1102_, 2, v___x_1101_);
lean_ctor_set(v___x_1102_, 3, v___x_1101_);
lean_ctor_set(v___x_1102_, 4, v___x_1101_);
lean_ctor_set(v___x_1102_, 5, v___x_1101_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = lean_obj_once(&l_Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l_Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l_Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
lean_ctor_set(v___x_1104_, 2, v___x_1103_);
lean_ctor_set(v___x_1104_, 3, v___x_1103_);
lean_ctor_set(v___x_1104_, 4, v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(lean_object* v___x_1105_, lean_object* v_declName_1106_, lean_object* v_stx_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; uint8_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v_args_1127_; lean_object* v___x_1128_; 
v___x_1111_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_1112_ = 0;
v___x_1113_ = lean_unsigned_to_nat(0u);
v___x_1114_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__9_spec__13_spec__14_spec__15_spec__16___redArg___closed__4);
v___x_1115_ = lean_obj_once(&l_Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l_Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l_Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1116_ = ((lean_object*)(l_Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_));
v___x_1117_ = lean_box(0);
v___x_1118_ = 1;
lean_inc(v___x_1105_);
v___x_1119_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1119_, 0, v___x_1111_);
lean_ctor_set(v___x_1119_, 1, v___x_1105_);
lean_ctor_set(v___x_1119_, 2, v___x_1115_);
lean_ctor_set(v___x_1119_, 3, v___x_1116_);
lean_ctor_set(v___x_1119_, 4, v___x_1117_);
lean_ctor_set(v___x_1119_, 5, v___x_1113_);
lean_ctor_set(v___x_1119_, 6, v___x_1117_);
lean_ctor_set_uint8(v___x_1119_, sizeof(void*)*7, v___x_1112_);
lean_ctor_set_uint8(v___x_1119_, sizeof(void*)*7 + 1, v___x_1112_);
lean_ctor_set_uint8(v___x_1119_, sizeof(void*)*7 + 2, v___x_1112_);
lean_ctor_set_uint8(v___x_1119_, sizeof(void*)*7 + 3, v___x_1118_);
v___x_1120_ = lean_obj_once(&l_Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l_Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l_Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1121_ = lean_obj_once(&l_Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l_Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l_Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1122_ = lean_obj_once(&l_Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l_Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l_Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1120_);
lean_ctor_set(v___x_1123_, 1, v___x_1121_);
lean_ctor_set(v___x_1123_, 2, v___x_1105_);
lean_ctor_set(v___x_1123_, 3, v___x_1114_);
lean_ctor_set(v___x_1123_, 4, v___x_1122_);
v___x_1124_ = lean_st_mk_ref(v___x_1123_);
v___x_1125_ = lean_unsigned_to_nat(1u);
v___x_1126_ = l_Lean_Syntax_getArg(v_stx_1107_, v___x_1125_);
v_args_1127_ = l_Lean_Syntax_getArgs(v___x_1126_);
lean_dec(v___x_1126_);
lean_inc(v___x_1124_);
v___x_1128_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs(v_declName_1106_, v_args_1127_, v___x_1119_, v___x_1124_, v___y_1108_, v___y_1109_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1137_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1131_ = v___x_1128_;
v_isShared_1132_ = v_isSharedCheck_1137_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1128_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1137_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1133_ = lean_st_ref_get(v___x_1124_);
lean_dec(v___x_1124_);
lean_dec(v___x_1133_);
if (v_isShared_1132_ == 0)
{
v___x_1135_ = v___x_1131_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1129_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
else
{
lean_dec(v___x_1124_);
return v___x_1128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object* v___x_1138_, lean_object* v_declName_1139_, lean_object* v_stx_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(v___x_1138_, v_declName_1139_, v_stx_1140_, v___y_1141_, v___y_1142_);
lean_dec(v_stx_1140_);
return v_res_1144_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(uint8_t v___x_1145_, lean_object* v_env_1146_, lean_object* v_n_1147_, lean_object* v_x_1148_){
_start:
{
uint8_t v___x_1149_; 
v___x_1149_ = l_Lean_Environment_contains(v_env_1146_, v_n_1147_, v___x_1145_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object* v___x_1150_, lean_object* v_env_1151_, lean_object* v_n_1152_, lean_object* v_x_1153_){
_start:
{
uint8_t v___x_586__boxed_1154_; uint8_t v_res_1155_; lean_object* v_r_1156_; 
v___x_586__boxed_1154_ = lean_unbox(v___x_1150_);
v_res_1155_ = l_Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(v___x_586__boxed_1154_, v_env_1151_, v_n_1152_, v_x_1153_);
lean_dec_ref(v_x_1153_);
v_r_1156_ = lean_box(v_res_1155_);
return v_r_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_));
v___x_1185_ = l_Lean_registerParametricAttribute___redArg(v___x_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_();
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1(){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1190_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_));
v___x_1191_ = ((lean_object*)(l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1___closed__0));
v___x_1192_ = l_Lean_addBuiltinDocString(v___x_1190_, v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1___boxed(lean_object* v_a_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1();
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3(){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_));
v___x_1222_ = ((lean_object*)(l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__6));
v___x_1223_ = l_Lean_addBuiltinDeclarationRanges(v___x_1221_, v___x_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___boxed(lean_object* v_a_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3();
return v_res_1225_;
}
}
static lean_object* _init_l_Lean_Compiler_getSpecializationArgs_x3f___closed__0(void){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Array_instInhabited(lean_box(0));
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getSpecializationArgs_x3f(lean_object* v_env_1227_, lean_object* v_declName_1228_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1229_ = lean_obj_once(&l_Lean_Compiler_getSpecializationArgs_x3f___closed__0, &l_Lean_Compiler_getSpecializationArgs_x3f___closed__0_once, _init_l_Lean_Compiler_getSpecializationArgs_x3f___closed__0);
v___x_1230_ = l_Lean_Compiler_specializeAttr;
v___x_1231_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_1229_, v___x_1230_, v_env_1227_, v_declName_1228_);
return v___x_1231_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_hasSpecializeAttribute(lean_object* v_env_1232_, lean_object* v_declName_1233_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_Compiler_getSpecializationArgs_x3f(v_env_1232_, v_declName_1233_);
if (lean_obj_tag(v___x_1234_) == 0)
{
uint8_t v___x_1235_; 
v___x_1235_ = 0;
return v___x_1235_;
}
else
{
uint8_t v___x_1236_; 
lean_dec_ref(v___x_1234_);
v___x_1236_ = 1;
return v___x_1236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasSpecializeAttribute___boxed(lean_object* v_env_1237_, lean_object* v_declName_1238_){
_start:
{
uint8_t v_res_1239_; lean_object* v_r_1240_; 
v_res_1239_ = l_Lean_Compiler_hasSpecializeAttribute(v_env_1237_, v_declName_1238_);
v_r_1240_ = lean_box(v_res_1239_);
return v_r_1240_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_hasNospecializeAttribute(lean_object* v_env_1241_, lean_object* v_declName_1242_){
_start:
{
lean_object* v___x_1243_; uint8_t v___x_1244_; 
v___x_1243_ = l_Lean_Compiler_nospecializeAttr;
v___x_1244_ = l_Lean_TagAttribute_hasTag(v___x_1243_, v_env_1241_, v_declName_1242_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasNospecializeAttribute___boxed(lean_object* v_env_1245_, lean_object* v_declName_1246_){
_start:
{
uint8_t v_res_1247_; lean_object* v_r_1248_; 
v_res_1247_ = l_Lean_Compiler_hasNospecializeAttribute(v_env_1245_, v_declName_1246_);
v_r_1248_ = lean_box(v_res_1247_);
return v_r_1248_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_Specialize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_instInhabitedSpecializeAttributeKind_default = _init_l_Lean_Compiler_instInhabitedSpecializeAttributeKind_default();
l_Lean_Compiler_instInhabitedSpecializeAttributeKind = _init_l_Lean_Compiler_instInhabitedSpecializeAttributeKind();
res = l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_nospecializeAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_nospecializeAttr);
lean_dec_ref(res);
res = l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_specializeAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_specializeAttr);
lean_dec_ref(res);
res = l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_Specialize(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Specialize(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Specialize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_Specialize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_Specialize(builtin);
}
#ifdef __cplusplus
}
#endif
