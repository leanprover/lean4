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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___redArg(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nospecialize"};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 38, 76, 194, 31, 149, 48, 135)}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "mark definition to never be specialized"};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "nospecializeAttr"};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 58, 232, 107, 183, 159, 132, 232)}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_nospecializeAttr;
static const lean_string_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "Marks a definition to never be specialized during code generation.\n"};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(78) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(78) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__4_value),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___boxed(lean_object*);
static const lean_string_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "weak_specialize"};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 190, 16, 147, 6, 108, 139, 204)}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 120, .m_capacity = 120, .m_length = 119, .m_data = "mark type for weak specialization: instances are only specialized when another argument already triggers specialization"};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "weakSpecializeAttr"};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(171, 136, 29, 200, 53, 12, 251, 84)}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_weakSpecializeAttr;
static const lean_string_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 300, .m_capacity = 300, .m_length = 299, .m_data = "Marks a type for weak specialization: Parameters of this type are only specialized when\nanother argument already triggers specialization. Unlike `@[nospecialize]`, if specialization\nhappens for other reasons, parameters of this type will participate in the specialization\nrather than being ignored.\n"};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)(((size_t)(125) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(125) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(34) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(34) << 1) | 1)),((lean_object*)(((size_t)(37) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__4_value),((lean_object*)(((size_t)(37) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "specializeAttr"};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 4, 174, 8, 190, 202, 8, 76)}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "specialize"};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(241, 143, 174, 76, 41, 16, 248, 244)}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "mark definition to always be specialized"};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_specializeAttr;
static const lean_string_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 750, .m_capacity = 750, .m_length = 749, .m_data = "Marks a definition to always be specialized during code generation.\n\nSpecialization is an optimization in the code generator for generating variants of a function that\nare specialized to specific parameter values. This is in particular useful for functions that take\nother functions as parameters: Usually when passing functions as parameters, a closure needs to be\nallocated that will then be called. Using `@[specialize]` prevents both of these operations by\nusing the provided function directly in the specialization of the inner function.\n\n`@[specialize]` can take additional arguments for the parameter names or indices (starting at 1) of\nthe parameters that should be specialized. By default, instance and function parameters are\nspecialized.\n"};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(64) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(85) << 1) | 1)),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(78) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(78) << 1) | 1)),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__4_value),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___boxed(lean_object*);
static lean_once_cell_t l_Lean_Compiler_getSpecializationArgs_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_getSpecializationArgs_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_getSpecializationArgs_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_hasSpecializeAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_hasSpecializeAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_hasNospecializeAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_hasNospecializeAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_hasWeakSpecializeAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_hasWeakSpecializeAttribute___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Compiler_SpecializeAttributeKind_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_Compiler_SpecializeAttributeKind_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_specialize_elim___redArg(lean_object* v_specialize_22_){
_start:
{
lean_inc(v_specialize_22_);
return v_specialize_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_specialize_elim___redArg___boxed(lean_object* v_specialize_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Compiler_SpecializeAttributeKind_specialize_elim___redArg(v_specialize_23_);
lean_dec(v_specialize_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_specialize_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_specialize_28_){
_start:
{
lean_inc(v_specialize_28_);
return v_specialize_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_specialize_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_specialize_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Compiler_SpecializeAttributeKind_specialize_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_specialize_32_);
lean_dec(v_specialize_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim___redArg(lean_object* v_nospecialize_35_){
_start:
{
lean_inc(v_nospecialize_35_);
return v_nospecialize_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim___redArg___boxed(lean_object* v_nospecialize_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim___redArg(v_nospecialize_36_);
lean_dec(v_nospecialize_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_nospecialize_41_){
_start:
{
lean_inc(v_nospecialize_41_);
return v_nospecialize_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_nospecialize_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_nospecialize_45_);
lean_dec(v_nospecialize_45_);
return v_res_47_;
}
}
static uint8_t _init_l_Lean_Compiler_instInhabitedSpecializeAttributeKind_default(void){
_start:
{
uint8_t v___x_48_; 
v___x_48_ = 0;
return v___x_48_;
}
}
static uint8_t _init_l_Lean_Compiler_instInhabitedSpecializeAttributeKind(void){
_start:
{
uint8_t v___x_49_; 
v___x_49_ = 0;
return v___x_49_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_instBEqSpecializeAttributeKind_beq(uint8_t v_x_50_, uint8_t v_y_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_52_ = l_Lean_Compiler_SpecializeAttributeKind_ctorIdx(v_x_50_);
v___x_53_ = l_Lean_Compiler_SpecializeAttributeKind_ctorIdx(v_y_51_);
v___x_54_ = lean_nat_dec_eq(v___x_52_, v___x_53_);
lean_dec(v___x_53_);
lean_dec(v___x_52_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_instBEqSpecializeAttributeKind_beq___boxed(lean_object* v_x_55_, lean_object* v_y_56_){
_start:
{
uint8_t v_x_21__boxed_57_; uint8_t v_y_22__boxed_58_; uint8_t v_res_59_; lean_object* v_r_60_; 
v_x_21__boxed_57_ = lean_unbox(v_x_55_);
v_y_22__boxed_58_ = lean_unbox(v_y_56_);
v_res_59_ = l_Lean_Compiler_instBEqSpecializeAttributeKind_beq(v_x_21__boxed_57_, v_y_22__boxed_58_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_(lean_object* v_x_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_box(0);
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2____boxed(lean_object* v_x_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_(v_x_69_, v___y_70_, v___y_71_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
lean_dec(v_x_69_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___f_87_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_88_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_89_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_90_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_91_ = 0;
v___x_92_ = lean_box(2);
v___x_93_ = l_Lean_registerTagAttribute(v___x_88_, v___x_89_, v___f_87_, v___x_90_, v___x_91_, v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2____boxed(lean_object* v_a_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_();
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1(){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_98_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_99_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1___closed__0));
v___x_100_ = l_Lean_addBuiltinDocString(v___x_98_, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1___boxed(lean_object* v_a_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1();
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3(){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_130_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__6));
v___x_131_ = l_Lean_addBuiltinDeclarationRanges(v___x_129_, v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___boxed(lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3();
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___f_144_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_145_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_));
v___x_146_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_));
v___x_147_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_));
v___x_148_ = 0;
v___x_149_ = lean_box(2);
v___x_150_ = l_Lean_registerTagAttribute(v___x_145_, v___x_146_, v___f_144_, v___x_147_, v___x_148_, v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2____boxed(lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_();
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1(){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_));
v___x_156_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1___closed__0));
v___x_157_ = l_Lean_addBuiltinDocString(v___x_155_, v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1___boxed(lean_object* v_a_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1();
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3(){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_));
v___x_187_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__6));
v___x_188_ = l_Lean_addBuiltinDeclarationRanges(v___x_186_, v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___boxed(lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3();
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0(lean_object* v_k_191_, lean_object* v_b_192_, lean_object* v_c_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v___x_199_; 
lean_inc(v___y_197_);
lean_inc_ref(v___y_196_);
lean_inc(v___y_195_);
lean_inc_ref(v___y_194_);
v___x_199_ = lean_apply_7(v_k_191_, v_b_192_, v_c_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, lean_box(0));
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0___boxed(lean_object* v_k_200_, lean_object* v_b_201_, lean_object* v_c_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0(v_k_200_, v_b_201_, v_c_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(lean_object* v_type_209_, lean_object* v_k_210_, uint8_t v_cleanupAnnotations_211_, uint8_t v_whnfType_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v___f_218_; lean_object* v___x_219_; 
v___f_218_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_218_, 0, v_k_210_);
v___x_219_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_209_, v___f_218_, v_cleanupAnnotations_211_, v_whnfType_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
v_a_220_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_219_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
else
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
v_a_228_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_219_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_219_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___boxed(lean_object* v_type_236_, lean_object* v_k_237_, lean_object* v_cleanupAnnotations_238_, lean_object* v_whnfType_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_245_; uint8_t v_whnfType_boxed_246_; lean_object* v_res_247_; 
v_cleanupAnnotations_boxed_245_ = lean_unbox(v_cleanupAnnotations_238_);
v_whnfType_boxed_246_ = lean_unbox(v_whnfType_239_);
v_res_247_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(v_type_236_, v_k_237_, v_cleanupAnnotations_boxed_245_, v_whnfType_boxed_246_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7(lean_object* v_00_u03b1_248_, lean_object* v_type_249_, lean_object* v_k_250_, uint8_t v_cleanupAnnotations_251_, uint8_t v_whnfType_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(v_type_249_, v_k_250_, v_cleanupAnnotations_251_, v_whnfType_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___boxed(lean_object* v_00_u03b1_259_, lean_object* v_type_260_, lean_object* v_k_261_, lean_object* v_cleanupAnnotations_262_, lean_object* v_whnfType_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_269_; uint8_t v_whnfType_boxed_270_; lean_object* v_res_271_; 
v_cleanupAnnotations_boxed_269_ = lean_unbox(v_cleanupAnnotations_262_);
v_whnfType_boxed_270_ = lean_unbox(v_whnfType_263_);
v_res_271_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7(v_00_u03b1_259_, v_type_260_, v_k_261_, v_cleanupAnnotations_boxed_269_, v_whnfType_boxed_270_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___redArg(lean_object* v_hi_272_, lean_object* v_pivot_273_, lean_object* v_as_274_, lean_object* v_i_275_, lean_object* v_k_276_){
_start:
{
uint8_t v___x_277_; 
v___x_277_ = lean_nat_dec_lt(v_k_276_, v_hi_272_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec(v_k_276_);
v___x_278_ = lean_array_fswap(v_as_274_, v_i_275_, v_hi_272_);
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v_i_275_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
return v___x_279_;
}
else
{
lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_280_ = lean_array_fget_borrowed(v_as_274_, v_k_276_);
v___x_281_ = lean_nat_dec_lt(v___x_280_, v_pivot_273_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = lean_nat_add(v_k_276_, v___x_282_);
lean_dec(v_k_276_);
v_k_276_ = v___x_283_;
goto _start;
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_285_ = lean_array_fswap(v_as_274_, v_i_275_, v_k_276_);
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_nat_add(v_i_275_, v___x_286_);
lean_dec(v_i_275_);
v___x_288_ = lean_nat_add(v_k_276_, v___x_286_);
lean_dec(v_k_276_);
v_as_274_ = v___x_285_;
v_i_275_ = v___x_287_;
v_k_276_ = v___x_288_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___redArg___boxed(lean_object* v_hi_290_, lean_object* v_pivot_291_, lean_object* v_as_292_, lean_object* v_i_293_, lean_object* v_k_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___redArg(v_hi_290_, v_pivot_291_, v_as_292_, v_i_293_, v_k_294_);
lean_dec(v_pivot_291_);
lean_dec(v_hi_290_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(lean_object* v_n_296_, lean_object* v_as_297_, lean_object* v_lo_298_, lean_object* v_hi_299_){
_start:
{
lean_object* v___y_301_; uint8_t v___x_311_; 
v___x_311_ = lean_nat_dec_lt(v_lo_298_, v_hi_299_);
if (v___x_311_ == 0)
{
lean_dec(v_lo_298_);
return v_as_297_;
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v_mid_314_; lean_object* v___y_316_; lean_object* v___y_322_; lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_312_ = lean_nat_add(v_lo_298_, v_hi_299_);
v___x_313_ = lean_unsigned_to_nat(1u);
v_mid_314_ = lean_nat_shiftr(v___x_312_, v___x_313_);
lean_dec(v___x_312_);
v___x_327_ = lean_array_fget_borrowed(v_as_297_, v_mid_314_);
v___x_328_ = lean_array_fget_borrowed(v_as_297_, v_lo_298_);
v___x_329_ = lean_nat_dec_lt(v___x_327_, v___x_328_);
if (v___x_329_ == 0)
{
v___y_322_ = v_as_297_;
goto v___jp_321_;
}
else
{
lean_object* v___x_330_; 
v___x_330_ = lean_array_fswap(v_as_297_, v_lo_298_, v_mid_314_);
v___y_322_ = v___x_330_;
goto v___jp_321_;
}
v___jp_315_:
{
lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_317_ = lean_array_fget_borrowed(v___y_316_, v_mid_314_);
v___x_318_ = lean_array_fget_borrowed(v___y_316_, v_hi_299_);
v___x_319_ = lean_nat_dec_lt(v___x_317_, v___x_318_);
if (v___x_319_ == 0)
{
lean_dec(v_mid_314_);
v___y_301_ = v___y_316_;
goto v___jp_300_;
}
else
{
lean_object* v___x_320_; 
v___x_320_ = lean_array_fswap(v___y_316_, v_mid_314_, v_hi_299_);
lean_dec(v_mid_314_);
v___y_301_ = v___x_320_;
goto v___jp_300_;
}
}
v___jp_321_:
{
lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_323_ = lean_array_fget_borrowed(v___y_322_, v_hi_299_);
v___x_324_ = lean_array_fget_borrowed(v___y_322_, v_lo_298_);
v___x_325_ = lean_nat_dec_lt(v___x_323_, v___x_324_);
if (v___x_325_ == 0)
{
v___y_316_ = v___y_322_;
goto v___jp_315_;
}
else
{
lean_object* v___x_326_; 
v___x_326_ = lean_array_fswap(v___y_322_, v_lo_298_, v_hi_299_);
v___y_316_ = v___x_326_;
goto v___jp_315_;
}
}
}
v___jp_300_:
{
lean_object* v_pivot_302_; lean_object* v___x_303_; lean_object* v_fst_304_; lean_object* v_snd_305_; uint8_t v___x_306_; 
v_pivot_302_ = lean_array_fget(v___y_301_, v_hi_299_);
lean_inc_n(v_lo_298_, 2);
v___x_303_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___redArg(v_hi_299_, v_pivot_302_, v___y_301_, v_lo_298_, v_lo_298_);
lean_dec(v_pivot_302_);
v_fst_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_fst_304_);
v_snd_305_ = lean_ctor_get(v___x_303_, 1);
lean_inc(v_snd_305_);
lean_dec_ref(v___x_303_);
v___x_306_ = lean_nat_dec_le(v_hi_299_, v_fst_304_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_307_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(v_n_296_, v_snd_305_, v_lo_298_, v_fst_304_);
v___x_308_ = lean_unsigned_to_nat(1u);
v___x_309_ = lean_nat_add(v_fst_304_, v___x_308_);
lean_dec(v_fst_304_);
v_as_297_ = v___x_307_;
v_lo_298_ = v___x_309_;
goto _start;
}
else
{
lean_dec(v_fst_304_);
lean_dec(v_lo_298_);
return v_snd_305_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg___boxed(lean_object* v_n_331_, lean_object* v_as_332_, lean_object* v_lo_333_, lean_object* v_hi_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(v_n_331_, v_as_332_, v_lo_333_, v_hi_334_);
lean_dec(v_hi_334_);
lean_dec(v_n_331_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg(size_t v_sz_336_, size_t v_i_337_, lean_object* v_bs_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
uint8_t v___x_343_; 
v___x_343_ = lean_usize_dec_lt(v_i_337_, v_sz_336_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; 
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v_bs_338_);
return v___x_344_;
}
else
{
lean_object* v_v_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_v_345_ = lean_array_uget_borrowed(v_bs_338_, v_i_337_);
v___x_346_ = l_Lean_Expr_fvarId_x21(v_v_345_);
v___x_347_ = l_Lean_FVarId_getUserName___redArg(v___x_346_, v___y_339_, v___y_340_, v___y_341_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_349_; lean_object* v_bs_x27_350_; size_t v___x_351_; size_t v___x_352_; lean_object* v___x_353_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_347_, 1);
v___x_349_ = lean_unsigned_to_nat(0u);
v_bs_x27_350_ = lean_array_uset(v_bs_338_, v_i_337_, v___x_349_);
v___x_351_ = ((size_t)1ULL);
v___x_352_ = lean_usize_add(v_i_337_, v___x_351_);
v___x_353_ = lean_array_uset(v_bs_x27_350_, v_i_337_, v_a_348_);
v_i_337_ = v___x_352_;
v_bs_338_ = v___x_353_;
goto _start;
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec_ref(v_bs_338_);
v_a_355_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_347_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_347_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg___boxed(lean_object* v_sz_363_, lean_object* v_i_364_, lean_object* v_bs_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
size_t v_sz_boxed_370_; size_t v_i_boxed_371_; lean_object* v_res_372_; 
v_sz_boxed_370_ = lean_unbox_usize(v_sz_363_);
lean_dec(v_sz_363_);
v_i_boxed_371_ = lean_unbox_usize(v_i_364_);
lean_dec(v_i_364_);
v_res_372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg(v_sz_boxed_370_, v_i_boxed_371_, v_bs_365_, v___y_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec_ref(v___y_366_);
return v_res_372_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1(lean_object* v_a_373_, lean_object* v_as_374_, size_t v_i_375_, size_t v_stop_376_){
_start:
{
uint8_t v___x_377_; 
v___x_377_ = lean_usize_dec_eq(v_i_375_, v_stop_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = lean_array_uget_borrowed(v_as_374_, v_i_375_);
v___x_379_ = lean_nat_dec_eq(v_a_373_, v___x_378_);
if (v___x_379_ == 0)
{
size_t v___x_380_; size_t v___x_381_; 
v___x_380_ = ((size_t)1ULL);
v___x_381_ = lean_usize_add(v_i_375_, v___x_380_);
v_i_375_ = v___x_381_;
goto _start;
}
else
{
return v___x_379_;
}
}
else
{
uint8_t v___x_383_; 
v___x_383_ = 0;
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1___boxed(lean_object* v_a_384_, lean_object* v_as_385_, lean_object* v_i_386_, lean_object* v_stop_387_){
_start:
{
size_t v_i_boxed_388_; size_t v_stop_boxed_389_; uint8_t v_res_390_; lean_object* v_r_391_; 
v_i_boxed_388_ = lean_unbox_usize(v_i_386_);
lean_dec(v_i_386_);
v_stop_boxed_389_ = lean_unbox_usize(v_stop_387_);
lean_dec(v_stop_387_);
v_res_390_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1(v_a_384_, v_as_385_, v_i_boxed_388_, v_stop_boxed_389_);
lean_dec_ref(v_as_385_);
lean_dec(v_a_384_);
v_r_391_ = lean_box(v_res_390_);
return v_r_391_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1(lean_object* v_as_392_, lean_object* v_a_393_){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_394_ = lean_unsigned_to_nat(0u);
v___x_395_ = lean_array_get_size(v_as_392_);
v___x_396_ = lean_nat_dec_lt(v___x_394_, v___x_395_);
if (v___x_396_ == 0)
{
return v___x_396_;
}
else
{
if (v___x_396_ == 0)
{
return v___x_396_;
}
else
{
size_t v___x_397_; size_t v___x_398_; uint8_t v___x_399_; 
v___x_397_ = ((size_t)0ULL);
v___x_398_ = lean_usize_of_nat(v___x_395_);
v___x_399_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1(v_a_393_, v_as_392_, v___x_397_, v___x_398_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1___boxed(lean_object* v_as_400_, lean_object* v_a_401_){
_start:
{
uint8_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1(v_as_400_, v_a_401_);
lean_dec(v_a_401_);
lean_dec_ref(v_as_400_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5_spec__8(lean_object* v_xs_404_, lean_object* v_v_405_, lean_object* v_i_406_){
_start:
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = lean_array_get_size(v_xs_404_);
v___x_408_ = lean_nat_dec_lt(v_i_406_, v___x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; 
lean_dec(v_i_406_);
v___x_409_ = lean_box(0);
return v___x_409_;
}
else
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_array_fget_borrowed(v_xs_404_, v_i_406_);
v___x_411_ = lean_name_eq(v___x_410_, v_v_405_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_unsigned_to_nat(1u);
v___x_413_ = lean_nat_add(v_i_406_, v___x_412_);
lean_dec(v_i_406_);
v_i_406_ = v___x_413_;
goto _start;
}
else
{
lean_object* v___x_415_; 
v___x_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_415_, 0, v_i_406_);
return v___x_415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_416_, lean_object* v_v_417_, lean_object* v_i_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5_spec__8(v_xs_416_, v_v_417_, v_i_418_);
lean_dec(v_v_417_);
lean_dec_ref(v_xs_416_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5(lean_object* v_xs_420_, lean_object* v_v_421_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5_spec__8(v_xs_420_, v_v_421_, v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5___boxed(lean_object* v_xs_424_, lean_object* v_v_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5(v_xs_424_, v_v_425_);
lean_dec(v_v_425_);
lean_dec_ref(v_xs_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3(lean_object* v_xs_427_, lean_object* v_v_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5(v_xs_427_, v_v_428_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v___x_430_; 
v___x_430_ = lean_box(0);
return v___x_430_;
}
else
{
lean_object* v_val_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
v_val_431_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_429_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_val_431_);
lean_dec(v___x_429_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_val_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3___boxed(lean_object* v_xs_439_, lean_object* v_v_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3(v_xs_439_, v_v_440_);
lean_dec(v_v_440_);
lean_dec_ref(v_xs_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5(lean_object* v_msgData_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___x_448_; lean_object* v_env_449_; lean_object* v___x_450_; lean_object* v_toCold_451_; lean_object* v_mctx_452_; lean_object* v_lctx_453_; lean_object* v_options_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_448_ = lean_st_ref_get(v___y_446_);
v_env_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc_ref(v_env_449_);
lean_dec(v___x_448_);
v___x_450_ = lean_st_ref_get(v___y_444_);
v_toCold_451_ = lean_ctor_get(v___y_445_, 0);
v_mctx_452_ = lean_ctor_get(v___x_450_, 0);
lean_inc_ref(v_mctx_452_);
lean_dec(v___x_450_);
v_lctx_453_ = lean_ctor_get(v___y_443_, 2);
v_options_454_ = lean_ctor_get(v_toCold_451_, 2);
lean_inc_ref(v_options_454_);
lean_inc_ref(v_lctx_453_);
v___x_455_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_455_, 0, v_env_449_);
lean_ctor_set(v___x_455_, 1, v_mctx_452_);
lean_ctor_set(v___x_455_, 2, v_lctx_453_);
lean_ctor_set(v___x_455_, 3, v_options_454_);
v___x_456_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v_msgData_442_);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5___boxed(lean_object* v_msgData_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5(v_msgData_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg(lean_object* v_msg_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_ref_471_; lean_object* v___x_472_; lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_481_; 
v_ref_471_ = lean_ctor_get(v___y_468_, 2);
v___x_472_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5(v_msg_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_481_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_481_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_481_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_479_; 
lean_inc(v_ref_471_);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v_ref_471_);
lean_ctor_set(v___x_477_, 1, v_a_473_);
if (v_isShared_476_ == 0)
{
lean_ctor_set_tag(v___x_475_, 1);
lean_ctor_set(v___x_475_, 0, v___x_477_);
v___x_479_ = v___x_475_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg___boxed(lean_object* v_msg_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg(v_msg_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(lean_object* v_ref_489_, lean_object* v_msg_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_toCold_496_; lean_object* v_currRecDepth_497_; lean_object* v_ref_498_; uint8_t v_diag_499_; uint8_t v_suppressElabErrors_500_; lean_object* v_ref_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_toCold_496_ = lean_ctor_get(v___y_493_, 0);
v_currRecDepth_497_ = lean_ctor_get(v___y_493_, 1);
v_ref_498_ = lean_ctor_get(v___y_493_, 2);
v_diag_499_ = lean_ctor_get_uint8(v___y_493_, sizeof(void*)*3);
v_suppressElabErrors_500_ = lean_ctor_get_uint8(v___y_493_, sizeof(void*)*3 + 1);
v_ref_501_ = l_Lean_replaceRef(v_ref_489_, v_ref_498_);
lean_inc(v_currRecDepth_497_);
lean_inc_ref(v_toCold_496_);
v___x_502_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_502_, 0, v_toCold_496_);
lean_ctor_set(v___x_502_, 1, v_currRecDepth_497_);
lean_ctor_set(v___x_502_, 2, v_ref_501_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*3, v_diag_499_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*3 + 1, v_suppressElabErrors_500_);
v___x_503_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg(v_msg_490_, v___y_491_, v___y_492_, v___x_502_, v___y_494_);
lean_dec_ref_known(v___x_502_, 3);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg___boxed(lean_object* v_ref_504_, lean_object* v_msg_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_ref_504_, v_msg_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v_ref_504_);
return v_res_511_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__0));
v___x_514_ = l_Lean_stringToMessageData(v___x_513_);
return v___x_514_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__2));
v___x_517_ = l_Lean_stringToMessageData(v___x_516_);
return v___x_517_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__4));
v___x_520_ = l_Lean_stringToMessageData(v___x_519_);
return v___x_520_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__6));
v___x_523_ = l_Lean_stringToMessageData(v___x_522_);
return v___x_523_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__8));
v___x_526_ = l_Lean_stringToMessageData(v___x_525_);
return v___x_526_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__10));
v___x_529_ = l_Lean_stringToMessageData(v___x_528_);
return v___x_529_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__12));
v___x_532_ = l_Lean_stringToMessageData(v___x_531_);
return v___x_532_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__14));
v___x_535_ = l_Lean_stringToMessageData(v___x_534_);
return v___x_535_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__16));
v___x_538_ = l_Lean_stringToMessageData(v___x_537_);
return v___x_538_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__18));
v___x_541_ = l_Lean_stringToMessageData(v___x_540_);
return v___x_541_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__20));
v___x_544_ = l_Lean_stringToMessageData(v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4(lean_object* v_a_545_, lean_object* v_declName_546_, lean_object* v___x_547_, lean_object* v_as_548_, size_t v_sz_549_, size_t v_i_550_, lean_object* v_b_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_a_558_; lean_object* v___y_563_; uint8_t v___x_565_; 
v___x_565_ = lean_usize_dec_lt(v_i_550_, v_sz_549_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; 
lean_dec(v_declName_546_);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v_b_551_);
return v___x_566_;
}
else
{
lean_object* v___x_567_; uint8_t v___x_568_; lean_object* v_a_569_; lean_object* v___x_570_; 
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_nat_dec_eq(v___x_547_, v___x_567_);
v_a_569_ = lean_array_uget_borrowed(v_as_548_, v_i_550_);
v___x_570_ = l_Lean_Syntax_isNatLit_x3f(v_a_569_);
if (lean_obj_tag(v___x_570_) == 1)
{
lean_object* v_val_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_648_; 
v_val_571_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_648_ == 0)
{
v___x_573_ = v___x_570_;
v_isShared_574_ = v_isSharedCheck_648_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_val_571_);
lean_dec(v___x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_648_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; uint8_t v___x_637_; 
v___x_637_ = lean_nat_dec_eq(v_val_571_, v___x_567_);
if (v___x_637_ == 0)
{
v___y_576_ = v___y_552_;
v___y_577_ = v___y_553_;
v___y_578_ = v___y_554_;
v___y_579_ = v___y_555_;
goto v___jp_575_;
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15);
v___x_639_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_569_, v___x_638_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_dec_ref_known(v___x_639_, 1);
v___y_576_ = v___y_552_;
v___y_577_ = v___y_553_;
v___y_578_ = v___y_554_;
v___y_579_ = v___y_555_;
goto v___jp_575_;
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_del_object(v___x_573_);
lean_dec(v_val_571_);
lean_dec_ref(v_b_551_);
lean_dec(v_declName_546_);
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
v___jp_575_:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_580_ = lean_unsigned_to_nat(1u);
v___x_581_ = lean_nat_sub(v_val_571_, v___x_580_);
lean_dec(v_val_571_);
v___x_582_ = lean_array_get_size(v_a_545_);
v___x_583_ = lean_nat_dec_le(v___x_582_, v___x_581_);
if (v___x_583_ == 0)
{
uint8_t v___x_584_; 
v___x_584_ = l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1(v_b_551_, v___x_581_);
if (v___x_584_ == 0)
{
lean_del_object(v___x_573_);
v___y_563_ = v___x_581_;
goto v___jp_562_;
}
else
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_585_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1);
v___x_586_ = lean_nat_add(v___x_581_, v___x_580_);
v___x_587_ = l_Nat_reprFast(v___x_586_);
if (v_isShared_574_ == 0)
{
lean_ctor_set_tag(v___x_573_, 3);
lean_ctor_set(v___x_573_, 0, v___x_587_);
v___x_589_ = v___x_573_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_587_);
v___x_589_ = v_reuseFailAlloc_608_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_590_ = l_Lean_MessageData_ofFormat(v___x_589_);
v___x_591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_585_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3);
v___x_593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_591_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = lean_array_fget_borrowed(v_a_545_, v___x_581_);
lean_inc(v___x_594_);
v___x_595_ = l_Lean_MessageData_ofName(v___x_594_);
v___x_596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_593_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5);
v___x_598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_569_, v___x_598_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_dec_ref_known(v___x_599_, 1);
v___y_563_ = v___x_581_;
goto v___jp_562_;
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_dec(v___x_581_);
lean_dec_ref(v_b_551_);
lean_dec(v_declName_546_);
v_a_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_609_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7);
v___x_610_ = l_Nat_reprFast(v___x_581_);
if (v_isShared_574_ == 0)
{
lean_ctor_set_tag(v___x_573_, 3);
lean_ctor_set(v___x_573_, 0, v___x_610_);
v___x_612_ = v___x_573_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_636_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_613_ = l_Lean_MessageData_ofFormat(v___x_612_);
v___x_614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_609_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9);
v___x_616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_614_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
lean_inc(v_declName_546_);
v___x_617_ = l_Lean_MessageData_ofConstName(v_declName_546_, v___x_568_);
v___x_618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_616_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v___x_619_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11);
v___x_620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = l_Nat_reprFast(v___x_582_);
v___x_622_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
v___x_623_ = l_Lean_MessageData_ofFormat(v___x_622_);
v___x_624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_620_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13);
v___x_626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_569_, v___x_626_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_dec_ref_known(v___x_627_, 1);
v_a_558_ = v_b_551_;
goto v___jp_557_;
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec_ref(v_b_551_);
lean_dec(v_declName_546_);
v_a_628_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_627_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
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
lean_object* v___x_649_; lean_object* v___x_650_; 
lean_dec(v___x_570_);
v___x_649_ = l_Lean_Syntax_getId(v_a_569_);
v___x_650_ = l_Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3(v_a_545_, v___x_649_);
if (lean_obj_tag(v___x_650_) == 1)
{
lean_object* v_val_651_; uint8_t v___x_654_; 
v_val_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_val_651_);
lean_dec_ref_known(v___x_650_, 1);
v___x_654_ = l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1(v_b_551_, v_val_651_);
if (v___x_654_ == 0)
{
lean_dec(v___x_649_);
goto v___jp_652_;
}
else
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_655_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17);
v___x_656_ = l_Lean_MessageData_ofName(v___x_649_);
v___x_657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_655_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19);
v___x_659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_657_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_569_, v___x_659_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_dec_ref_known(v___x_660_, 1);
goto v___jp_652_;
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec(v_val_651_);
lean_dec_ref(v_b_551_);
lean_dec(v_declName_546_);
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_660_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
v___jp_652_:
{
lean_object* v___x_653_; 
v___x_653_ = lean_array_push(v_b_551_, v_val_651_);
v_a_558_ = v___x_653_;
goto v___jp_557_;
}
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
lean_dec(v___x_650_);
v___x_669_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17);
v___x_670_ = l_Lean_MessageData_ofName(v___x_649_);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9);
v___x_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
lean_inc(v_declName_546_);
v___x_674_ = l_Lean_MessageData_ofConstName(v_declName_546_, v___x_568_);
v___x_675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_673_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21);
v___x_677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_675_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_569_, v___x_677_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_dec_ref_known(v___x_678_, 1);
v_a_558_ = v_b_551_;
goto v___jp_557_;
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref(v_b_551_);
lean_dec(v_declName_546_);
v_a_679_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_678_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_678_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
}
v___jp_557_:
{
size_t v___x_559_; size_t v___x_560_; 
v___x_559_ = ((size_t)1ULL);
v___x_560_ = lean_usize_add(v_i_550_, v___x_559_);
v_i_550_ = v___x_560_;
v_b_551_ = v_a_558_;
goto _start;
}
v___jp_562_:
{
lean_object* v___x_564_; 
v___x_564_ = lean_array_push(v_b_551_, v___y_563_);
v_a_558_ = v___x_564_;
goto v___jp_557_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___boxed(lean_object* v_a_687_, lean_object* v_declName_688_, lean_object* v___x_689_, lean_object* v_as_690_, lean_object* v_sz_691_, lean_object* v_i_692_, lean_object* v_b_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
size_t v_sz_boxed_699_; size_t v_i_boxed_700_; lean_object* v_res_701_; 
v_sz_boxed_699_ = lean_unbox_usize(v_sz_691_);
lean_dec(v_sz_691_);
v_i_boxed_700_ = lean_unbox_usize(v_i_692_);
lean_dec(v_i_692_);
v_res_701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4(v_a_687_, v_declName_688_, v___x_689_, v_as_690_, v_sz_boxed_699_, v_i_boxed_700_, v_b_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec_ref(v_as_690_);
lean_dec(v___x_689_);
lean_dec_ref(v_a_687_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0(lean_object* v___x_702_, lean_object* v_args_703_, lean_object* v_declName_704_, lean_object* v___x_705_, lean_object* v_xs_706_, lean_object* v_x_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
size_t v_sz_713_; size_t v___x_714_; lean_object* v___x_715_; 
v_sz_713_ = lean_array_size(v_xs_706_);
v___x_714_ = ((size_t)0ULL);
v___x_715_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg(v_sz_713_, v___x_714_, v_xs_706_, v___y_708_, v___y_710_, v___y_711_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_739_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_739_ == 0)
{
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_739_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_739_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; size_t v_sz_721_; lean_object* v___x_722_; 
v___x_720_ = lean_mk_empty_array_with_capacity(v___x_702_);
v_sz_721_ = lean_array_size(v_args_703_);
v___x_722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4(v_a_716_, v_declName_704_, v___x_705_, v_args_703_, v_sz_721_, v___x_714_, v___x_720_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
lean_dec(v_a_716_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_724_; lean_object* v___y_726_; lean_object* v___y_727_; uint8_t v___x_732_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_723_);
v___x_724_ = lean_array_get_size(v_a_723_);
v___x_732_ = lean_nat_dec_eq(v___x_724_, v___x_702_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___y_736_; uint8_t v___x_738_; 
lean_dec_ref_known(v___x_722_, 1);
v___x_733_ = lean_unsigned_to_nat(1u);
v___x_734_ = lean_nat_sub(v___x_724_, v___x_733_);
v___x_738_ = lean_nat_dec_le(v___x_702_, v___x_734_);
if (v___x_738_ == 0)
{
lean_dec(v___x_702_);
lean_inc(v___x_734_);
v___y_736_ = v___x_734_;
goto v___jp_735_;
}
else
{
v___y_736_ = v___x_702_;
goto v___jp_735_;
}
v___jp_735_:
{
uint8_t v___x_737_; 
v___x_737_ = lean_nat_dec_le(v___y_736_, v___x_734_);
if (v___x_737_ == 0)
{
lean_dec(v___x_734_);
lean_inc(v___y_736_);
v___y_726_ = v___y_736_;
v___y_727_ = v___y_736_;
goto v___jp_725_;
}
else
{
v___y_726_ = v___y_736_;
v___y_727_ = v___x_734_;
goto v___jp_725_;
}
}
}
else
{
lean_dec(v_a_723_);
lean_del_object(v___x_718_);
lean_dec(v___x_702_);
return v___x_722_;
}
v___jp_725_:
{
lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_728_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(v___x_724_, v_a_723_, v___y_726_, v___y_727_);
lean_dec(v___y_727_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_728_);
v___x_730_ = v___x_718_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
else
{
lean_del_object(v___x_718_);
lean_dec(v___x_702_);
return v___x_722_;
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec(v_declName_704_);
lean_dec(v___x_702_);
v_a_740_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_715_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_715_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0___boxed(lean_object* v___x_748_, lean_object* v_args_749_, lean_object* v_declName_750_, lean_object* v___x_751_, lean_object* v_xs_752_, lean_object* v_x_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0(v___x_748_, v_args_749_, v_declName_750_, v___x_751_, v_xs_752_, v_x_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec_ref(v_x_753_);
lean_dec(v___x_751_);
lean_dec_ref(v_args_749_);
return v_res_759_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0(void){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_760_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0);
v___x_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
return v___x_762_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__2(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1);
v___x_764_ = lean_unsigned_to_nat(0u);
v___x_765_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
lean_ctor_set(v___x_765_, 2, v___x_764_);
lean_ctor_set(v___x_765_, 3, v___x_764_);
lean_ctor_set(v___x_765_, 4, v___x_763_);
lean_ctor_set(v___x_765_, 5, v___x_763_);
lean_ctor_set(v___x_765_, 6, v___x_763_);
lean_ctor_set(v___x_765_, 7, v___x_763_);
lean_ctor_set(v___x_765_, 8, v___x_763_);
lean_ctor_set(v___x_765_, 9, v___x_763_);
lean_ctor_set(v___x_765_, 10, v___x_763_);
return v___x_765_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = lean_unsigned_to_nat(32u);
v___x_767_ = lean_mk_empty_array_with_capacity(v___x_766_);
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
return v___x_768_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4(void){
_start:
{
size_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_769_ = ((size_t)5ULL);
v___x_770_ = lean_unsigned_to_nat(0u);
v___x_771_ = lean_unsigned_to_nat(32u);
v___x_772_ = lean_mk_empty_array_with_capacity(v___x_771_);
v___x_773_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__3);
v___x_774_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v___x_772_);
lean_ctor_set(v___x_774_, 2, v___x_770_);
lean_ctor_set(v___x_774_, 3, v___x_770_);
lean_ctor_set_usize(v___x_774_, 4, v___x_769_);
return v___x_774_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__5(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_775_ = lean_box(1);
v___x_776_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4);
v___x_777_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1);
v___x_778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v___x_776_);
lean_ctor_set(v___x_778_, 2, v___x_775_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__6));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__9(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__8));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__11(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__10));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__13(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__12));
v___x_790_ = l_Lean_stringToMessageData(v___x_789_);
return v___x_790_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__15(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__14));
v___x_793_ = l_Lean_stringToMessageData(v___x_792_);
return v___x_793_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__17(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__16));
v___x_796_ = l_Lean_stringToMessageData(v___x_795_);
return v___x_796_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__19(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__18));
v___x_799_ = l_Lean_stringToMessageData(v___x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg(lean_object* v_msg_800_, lean_object* v_declHint_801_, lean_object* v___y_802_){
_start:
{
lean_object* v___x_804_; lean_object* v_env_805_; uint8_t v___x_806_; 
v___x_804_ = lean_st_ref_get(v___y_802_);
v_env_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc_ref(v_env_805_);
lean_dec(v___x_804_);
v___x_806_ = l_Lean_Name_isAnonymous(v_declHint_801_);
if (v___x_806_ == 0)
{
uint8_t v_isExporting_807_; 
v_isExporting_807_ = lean_ctor_get_uint8(v_env_805_, sizeof(void*)*8);
if (v_isExporting_807_ == 0)
{
lean_object* v___x_808_; 
lean_dec_ref(v_env_805_);
lean_dec(v_declHint_801_);
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v_msg_800_);
return v___x_808_;
}
else
{
lean_object* v___x_809_; uint8_t v___x_810_; 
lean_inc_ref(v_env_805_);
v___x_809_ = l_Lean_Environment_setExporting(v_env_805_, v___x_806_);
lean_inc(v_declHint_801_);
lean_inc_ref(v___x_809_);
v___x_810_ = l_Lean_Environment_contains(v___x_809_, v_declHint_801_, v_isExporting_807_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; 
lean_dec_ref(v___x_809_);
lean_dec_ref(v_env_805_);
lean_dec(v_declHint_801_);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v_msg_800_);
return v___x_811_;
}
else
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v_c_817_; lean_object* v___x_818_; 
v___x_812_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__2);
v___x_813_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__5);
v___x_814_ = l_Lean_Options_empty;
v___x_815_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_815_, 0, v___x_809_);
lean_ctor_set(v___x_815_, 1, v___x_812_);
lean_ctor_set(v___x_815_, 2, v___x_813_);
lean_ctor_set(v___x_815_, 3, v___x_814_);
lean_inc(v_declHint_801_);
v___x_816_ = l_Lean_MessageData_ofConstName(v_declHint_801_, v___x_806_);
v_c_817_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_817_, 0, v___x_815_);
lean_ctor_set(v_c_817_, 1, v___x_816_);
v___x_818_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_805_, v_declHint_801_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
lean_dec_ref(v_env_805_);
lean_dec(v_declHint_801_);
v___x_819_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7);
v___x_820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
lean_ctor_set(v___x_820_, 1, v_c_817_);
v___x_821_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__9);
v___x_822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_820_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = l_Lean_MessageData_note(v___x_822_);
v___x_824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_824_, 0, v_msg_800_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
return v___x_825_;
}
else
{
lean_object* v_val_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_861_; 
v_val_826_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_861_ == 0)
{
v___x_828_ = v___x_818_;
v_isShared_829_ = v_isSharedCheck_861_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_val_826_);
lean_dec(v___x_818_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_861_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v_mod_833_; uint8_t v___x_834_; 
v___x_830_ = lean_box(0);
v___x_831_ = l_Lean_Environment_header(v_env_805_);
lean_dec_ref(v_env_805_);
v___x_832_ = l_Lean_EnvironmentHeader_moduleNames(v___x_831_);
v_mod_833_ = lean_array_get(v___x_830_, v___x_832_, v_val_826_);
lean_dec(v_val_826_);
lean_dec_ref(v___x_832_);
v___x_834_ = l_Lean_isPrivateName(v_declHint_801_);
lean_dec(v_declHint_801_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_835_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__11);
v___x_836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
lean_ctor_set(v___x_836_, 1, v_c_817_);
v___x_837_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__13);
v___x_838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_836_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = l_Lean_MessageData_ofName(v_mod_833_);
v___x_840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_838_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__15);
v___x_842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_840_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = l_Lean_MessageData_note(v___x_842_);
v___x_844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_844_, 0, v_msg_800_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
if (v_isShared_829_ == 0)
{
lean_ctor_set_tag(v___x_828_, 0);
lean_ctor_set(v___x_828_, 0, v___x_844_);
v___x_846_ = v___x_828_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_848_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7);
v___x_849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v_c_817_);
v___x_850_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__17);
v___x_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = l_Lean_MessageData_ofName(v_mod_833_);
v___x_853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_851_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__19);
v___x_855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = l_Lean_MessageData_note(v___x_855_);
v___x_857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_857_, 0, v_msg_800_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
if (v_isShared_829_ == 0)
{
lean_ctor_set_tag(v___x_828_, 0);
lean_ctor_set(v___x_828_, 0, v___x_857_);
v___x_859_ = v___x_828_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_862_; 
lean_dec_ref(v_env_805_);
lean_dec(v_declHint_801_);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v_msg_800_);
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___boxed(lean_object* v_msg_863_, lean_object* v_declHint_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg(v_msg_863_, v_declHint_864_, v___y_865_);
lean_dec(v___y_865_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16(lean_object* v_msg_868_, lean_object* v_declHint_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v___x_875_; lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_885_; 
v___x_875_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg(v_msg_868_, v_declHint_869_, v___y_873_);
v_a_876_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_885_ == 0)
{
v___x_878_ = v___x_875_;
v_isShared_879_ = v_isSharedCheck_885_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_875_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_885_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_880_ = l_Lean_unknownIdentifierMessageTag;
v___x_881_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
lean_ctor_set(v___x_881_, 1, v_a_876_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v___x_881_);
v___x_883_ = v___x_878_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16___boxed(lean_object* v_msg_886_, lean_object* v_declHint_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16(v_msg_886_, v_declHint_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg(lean_object* v_ref_894_, lean_object* v_msg_895_, lean_object* v_declHint_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v___x_902_; lean_object* v_a_903_; lean_object* v___x_904_; 
v___x_902_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16(v_msg_895_, v_declHint_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref(v___x_902_);
v___x_904_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_ref_894_, v_a_903_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg___boxed(lean_object* v_ref_905_, lean_object* v_msg_906_, lean_object* v_declHint_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg(v_ref_905_, v_msg_906_, v_declHint_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v_ref_905_);
return v_res_913_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__1(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__0));
v___x_916_ = l_Lean_stringToMessageData(v___x_915_);
return v___x_916_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__2));
v___x_919_ = l_Lean_stringToMessageData(v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg(lean_object* v_ref_920_, lean_object* v_constName_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; uint8_t v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_927_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__1);
v___x_928_ = 0;
lean_inc(v_constName_921_);
v___x_929_ = l_Lean_MessageData_ofConstName(v_constName_921_, v___x_928_);
v___x_930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_927_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__3);
v___x_932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_930_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg(v_ref_920_, v___x_932_, v_constName_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___boxed(lean_object* v_ref_934_, lean_object* v_constName_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg(v_ref_934_, v_constName_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v_ref_934_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg(lean_object* v_constName_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_ref_948_; lean_object* v___x_949_; 
v_ref_948_ = lean_ctor_get(v___y_945_, 2);
v___x_949_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg(v_ref_948_, v_constName_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg___boxed(lean_object* v_constName_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg(v_constName_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6(lean_object* v_constName_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v___x_963_; lean_object* v_env_964_; uint8_t v___x_965_; lean_object* v___x_966_; 
v___x_963_ = lean_st_ref_get(v___y_961_);
v_env_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc_ref(v_env_964_);
lean_dec(v___x_963_);
v___x_965_ = 0;
lean_inc(v_constName_957_);
v___x_966_ = l_Lean_Environment_find_x3f(v_env_964_, v_constName_957_, v___x_965_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg(v_constName_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
return v___x_967_;
}
else
{
lean_object* v_val_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
lean_dec(v_constName_957_);
v_val_968_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_966_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_val_968_);
lean_dec(v___x_966_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set_tag(v___x_970_, 0);
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_val_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6___boxed(lean_object* v_constName_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6(v_constName_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs(lean_object* v_declName_985_, lean_object* v_args_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_992_ = lean_array_get_size(v_args_986_);
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = lean_nat_dec_eq(v___x_992_, v___x_993_);
if (v___x_994_ == 0)
{
lean_object* v___x_995_; 
lean_inc(v_declName_985_);
v___x_995_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6(v_declName_985_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___f_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_995_, 1);
v___f_997_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0___boxed), 11, 4);
lean_closure_set(v___f_997_, 0, v___x_993_);
lean_closure_set(v___f_997_, 1, v_args_986_);
lean_closure_set(v___f_997_, 2, v_declName_985_);
lean_closure_set(v___f_997_, 3, v___x_992_);
v___x_998_ = l_Lean_ConstantInfo_type(v_a_996_);
lean_dec(v_a_996_);
v___x_999_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(v___x_998_, v___f_997_, v___x_994_, v___x_994_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
return v___x_999_;
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec_ref(v_args_986_);
lean_dec(v_declName_985_);
v_a_1000_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_995_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_995_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_dec_ref(v_args_986_);
lean_dec(v_declName_985_);
v___x_1008_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___closed__0));
v___x_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
return v___x_1009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___boxed(lean_object* v_declName_1010_, lean_object* v_args_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs(v_declName_1010_, v_args_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0(size_t v_sz_1018_, size_t v_i_1019_, lean_object* v_bs_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg(v_sz_1018_, v_i_1019_, v_bs_1020_, v___y_1021_, v___y_1023_, v___y_1024_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___boxed(lean_object* v_sz_1027_, lean_object* v_i_1028_, lean_object* v_bs_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
size_t v_sz_boxed_1035_; size_t v_i_boxed_1036_; lean_object* v_res_1037_; 
v_sz_boxed_1035_ = lean_unbox_usize(v_sz_1027_);
lean_dec(v_sz_1027_);
v_i_boxed_1036_ = lean_unbox_usize(v_i_1028_);
lean_dec(v_i_1028_);
v_res_1037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0(v_sz_boxed_1035_, v_i_boxed_1036_, v_bs_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2(lean_object* v_00_u03b1_1038_, lean_object* v_ref_1039_, lean_object* v_msg_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_ref_1039_, v_msg_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___boxed(lean_object* v_00_u03b1_1047_, lean_object* v_ref_1048_, lean_object* v_msg_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2(v_00_u03b1_1047_, v_ref_1048_, v_msg_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v_ref_1048_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5(lean_object* v_n_1056_, lean_object* v_as_1057_, lean_object* v_lo_1058_, lean_object* v_hi_1059_, lean_object* v_w_1060_, lean_object* v_hlo_1061_, lean_object* v_hhi_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(v_n_1056_, v_as_1057_, v_lo_1058_, v_hi_1059_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___boxed(lean_object* v_n_1064_, lean_object* v_as_1065_, lean_object* v_lo_1066_, lean_object* v_hi_1067_, lean_object* v_w_1068_, lean_object* v_hlo_1069_, lean_object* v_hhi_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5(v_n_1064_, v_as_1065_, v_lo_1066_, v_hi_1067_, v_w_1068_, v_hlo_1069_, v_hhi_1070_);
lean_dec(v_hi_1067_);
lean_dec(v_n_1064_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3(lean_object* v_00_u03b1_1072_, lean_object* v_msg_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg(v_msg_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1080_, lean_object* v_msg_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3(v_00_u03b1_1080_, v_msg_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8(lean_object* v_n_1088_, lean_object* v_lo_1089_, lean_object* v_hi_1090_, lean_object* v_hhi_1091_, lean_object* v_pivot_1092_, lean_object* v_as_1093_, lean_object* v_i_1094_, lean_object* v_k_1095_, lean_object* v_ilo_1096_, lean_object* v_ik_1097_, lean_object* v_w_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___redArg(v_hi_1090_, v_pivot_1092_, v_as_1093_, v_i_1094_, v_k_1095_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___boxed(lean_object* v_n_1100_, lean_object* v_lo_1101_, lean_object* v_hi_1102_, lean_object* v_hhi_1103_, lean_object* v_pivot_1104_, lean_object* v_as_1105_, lean_object* v_i_1106_, lean_object* v_k_1107_, lean_object* v_ilo_1108_, lean_object* v_ik_1109_, lean_object* v_w_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8(v_n_1100_, v_lo_1101_, v_hi_1102_, v_hhi_1103_, v_pivot_1104_, v_as_1105_, v_i_1106_, v_k_1107_, v_ilo_1108_, v_ik_1109_, v_w_1110_);
lean_dec(v_pivot_1104_);
lean_dec(v_hi_1102_);
lean_dec(v_lo_1101_);
lean_dec(v_n_1100_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10(lean_object* v_00_u03b1_1112_, lean_object* v_constName_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg(v_constName_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___boxed(lean_object* v_00_u03b1_1120_, lean_object* v_constName_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10(v_00_u03b1_1120_, v_constName_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14(lean_object* v_00_u03b1_1128_, lean_object* v_ref_1129_, lean_object* v_constName_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg(v_ref_1129_, v_constName_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___boxed(lean_object* v_00_u03b1_1137_, lean_object* v_ref_1138_, lean_object* v_constName_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14(v_00_u03b1_1137_, v_ref_1138_, v_constName_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v_ref_1138_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15(lean_object* v_00_u03b1_1146_, lean_object* v_ref_1147_, lean_object* v_msg_1148_, lean_object* v_declHint_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg(v_ref_1147_, v_msg_1148_, v_declHint_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___boxed(lean_object* v_00_u03b1_1156_, lean_object* v_ref_1157_, lean_object* v_msg_1158_, lean_object* v_declHint_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15(v_00_u03b1_1156_, v_ref_1157_, v_msg_1158_, v_declHint_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v_ref_1157_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17(lean_object* v_msg_1166_, lean_object* v_declHint_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg(v_msg_1166_, v_declHint_1167_, v___y_1171_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___boxed(lean_object* v_msg_1174_, lean_object* v_declHint_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17(v_msg_1174_, v_declHint_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(lean_object* v_x_1182_, lean_object* v_x_1183_, lean_object* v_x_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = lean_box(0);
v___x_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object* v_x_1189_, lean_object* v_x_1190_, lean_object* v_x_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(v_x_1189_, v_x_1190_, v_x_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v_x_1191_);
lean_dec_ref(v_x_1190_);
lean_dec(v_x_1189_);
return v_res_1194_;
}
}
static uint64_t _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1201_; uint64_t v___x_1202_; 
v___x_1201_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_));
v___x_1202_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1201_);
return v___x_1202_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1203_ = lean_uint64_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1204_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_));
v___x_1205_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
lean_ctor_set_uint64(v___x_1205_, sizeof(void*)*1, v___x_1203_);
return v___x_1205_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1206_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1209_ = lean_box(1);
v___x_1210_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4);
v___x_1211_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1212_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
lean_ctor_set(v___x_1212_, 1, v___x_1210_);
lean_ctor_set(v___x_1212_, 2, v___x_1209_);
return v___x_1212_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1216_ = lean_unsigned_to_nat(0u);
v___x_1217_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
lean_ctor_set(v___x_1217_, 2, v___x_1216_);
lean_ctor_set(v___x_1217_, 3, v___x_1216_);
lean_ctor_set(v___x_1217_, 4, v___x_1215_);
lean_ctor_set(v___x_1217_, 5, v___x_1215_);
lean_ctor_set(v___x_1217_, 6, v___x_1215_);
lean_ctor_set(v___x_1217_, 7, v___x_1215_);
lean_ctor_set(v___x_1217_, 8, v___x_1215_);
lean_ctor_set(v___x_1217_, 9, v___x_1215_);
lean_ctor_set(v___x_1217_, 10, v___x_1215_);
return v___x_1217_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1219_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
lean_ctor_set(v___x_1219_, 2, v___x_1218_);
lean_ctor_set(v___x_1219_, 3, v___x_1218_);
lean_ctor_set(v___x_1219_, 4, v___x_1218_);
lean_ctor_set(v___x_1219_, 5, v___x_1218_);
return v___x_1219_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
lean_ctor_set(v___x_1221_, 2, v___x_1220_);
lean_ctor_set(v___x_1221_, 3, v___x_1220_);
lean_ctor_set(v___x_1221_, 4, v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(lean_object* v___x_1222_, lean_object* v_declName_1223_, lean_object* v_stx_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
uint8_t v___x_1228_; uint8_t v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v_args_1244_; lean_object* v___x_1245_; 
v___x_1228_ = 0;
v___x_1229_ = 1;
v___x_1230_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1231_ = lean_unsigned_to_nat(0u);
v___x_1232_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4);
v___x_1233_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1234_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_));
v___x_1235_ = lean_box(0);
lean_inc(v___x_1222_);
v___x_1236_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1236_, 0, v___x_1230_);
lean_ctor_set(v___x_1236_, 1, v___x_1222_);
lean_ctor_set(v___x_1236_, 2, v___x_1233_);
lean_ctor_set(v___x_1236_, 3, v___x_1234_);
lean_ctor_set(v___x_1236_, 4, v___x_1235_);
lean_ctor_set(v___x_1236_, 5, v___x_1231_);
lean_ctor_set(v___x_1236_, 6, v___x_1235_);
lean_ctor_set_uint8(v___x_1236_, sizeof(void*)*7, v___x_1228_);
lean_ctor_set_uint8(v___x_1236_, sizeof(void*)*7 + 1, v___x_1228_);
lean_ctor_set_uint8(v___x_1236_, sizeof(void*)*7 + 2, v___x_1228_);
lean_ctor_set_uint8(v___x_1236_, sizeof(void*)*7 + 3, v___x_1229_);
v___x_1237_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1238_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1239_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1237_);
lean_ctor_set(v___x_1240_, 1, v___x_1238_);
lean_ctor_set(v___x_1240_, 2, v___x_1222_);
lean_ctor_set(v___x_1240_, 3, v___x_1232_);
lean_ctor_set(v___x_1240_, 4, v___x_1239_);
v___x_1241_ = lean_st_mk_ref(v___x_1240_);
v___x_1242_ = lean_unsigned_to_nat(1u);
v___x_1243_ = l_Lean_Syntax_getArg(v_stx_1224_, v___x_1242_);
v_args_1244_ = l_Lean_Syntax_getArgs(v___x_1243_);
lean_dec(v___x_1243_);
v___x_1245_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs(v_declName_1223_, v_args_1244_, v___x_1236_, v___x_1241_, v___y_1225_, v___y_1226_);
lean_dec_ref_known(v___x_1236_, 7);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1254_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1248_ = v___x_1245_;
v_isShared_1249_ = v_isSharedCheck_1254_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1254_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1250_ = lean_st_ref_get(v___x_1241_);
lean_dec(v___x_1241_);
lean_dec(v___x_1250_);
if (v_isShared_1249_ == 0)
{
v___x_1252_ = v___x_1248_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1246_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
else
{
lean_dec(v___x_1241_);
return v___x_1245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object* v___x_1255_, lean_object* v_declName_1256_, lean_object* v_stx_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(v___x_1255_, v_declName_1256_, v_stx_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v_stx_1257_);
return v_res_1261_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(uint8_t v___x_1262_, lean_object* v_env_1263_, lean_object* v_n_1264_, lean_object* v_x_1265_){
_start:
{
uint8_t v___x_1266_; 
v___x_1266_ = l_Lean_Environment_contains(v_env_1263_, v_n_1264_, v___x_1262_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object* v___x_1267_, lean_object* v_env_1268_, lean_object* v_n_1269_, lean_object* v_x_1270_){
_start:
{
uint8_t v___x_563__boxed_1271_; uint8_t v_res_1272_; lean_object* v_r_1273_; 
v___x_563__boxed_1271_ = lean_unbox(v___x_1267_);
v_res_1272_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(v___x_563__boxed_1271_, v_env_1268_, v_n_1269_, v_x_1270_);
lean_dec_ref(v_x_1270_);
v_r_1273_ = lean_box(v_res_1272_);
return v_r_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_));
v___x_1302_ = l_Lean_registerParametricAttribute___redArg(v___x_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object* v_a_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_();
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1(){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1307_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_));
v___x_1308_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1___closed__0));
v___x_1309_ = l_Lean_addBuiltinDocString(v___x_1307_, v___x_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1___boxed(lean_object* v_a_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1();
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3(){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1338_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_));
v___x_1339_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__6));
v___x_1340_ = l_Lean_addBuiltinDeclarationRanges(v___x_1338_, v___x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___boxed(lean_object* v_a_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3();
return v_res_1342_;
}
}
static lean_object* _init_l_Lean_Compiler_getSpecializationArgs_x3f___closed__0(void){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Array_instInhabited(lean_box(0));
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getSpecializationArgs_x3f(lean_object* v_env_1344_, lean_object* v_declName_1345_){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1346_ = lean_obj_once(&l_Lean_Compiler_getSpecializationArgs_x3f___closed__0, &l_Lean_Compiler_getSpecializationArgs_x3f___closed__0_once, _init_l_Lean_Compiler_getSpecializationArgs_x3f___closed__0);
v___x_1347_ = l_Lean_Compiler_specializeAttr;
v___x_1348_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_1346_, v___x_1347_, v_env_1344_, v_declName_1345_);
return v___x_1348_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_hasSpecializeAttribute(lean_object* v_env_1349_, lean_object* v_declName_1350_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_Compiler_getSpecializationArgs_x3f(v_env_1349_, v_declName_1350_);
if (lean_obj_tag(v___x_1351_) == 0)
{
uint8_t v___x_1352_; 
v___x_1352_ = 0;
return v___x_1352_;
}
else
{
uint8_t v___x_1353_; 
lean_dec_ref_known(v___x_1351_, 1);
v___x_1353_ = 1;
return v___x_1353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasSpecializeAttribute___boxed(lean_object* v_env_1354_, lean_object* v_declName_1355_){
_start:
{
uint8_t v_res_1356_; lean_object* v_r_1357_; 
v_res_1356_ = l_Lean_Compiler_hasSpecializeAttribute(v_env_1354_, v_declName_1355_);
v_r_1357_ = lean_box(v_res_1356_);
return v_r_1357_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_hasNospecializeAttribute(lean_object* v_env_1358_, lean_object* v_declName_1359_){
_start:
{
lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1360_ = l_Lean_Compiler_nospecializeAttr;
v___x_1361_ = l_Lean_TagAttribute_hasTag(v___x_1360_, v_env_1358_, v_declName_1359_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasNospecializeAttribute___boxed(lean_object* v_env_1362_, lean_object* v_declName_1363_){
_start:
{
uint8_t v_res_1364_; lean_object* v_r_1365_; 
v_res_1364_ = l_Lean_Compiler_hasNospecializeAttribute(v_env_1362_, v_declName_1363_);
v_r_1365_ = lean_box(v_res_1364_);
return v_r_1365_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_hasWeakSpecializeAttribute(lean_object* v_env_1366_, lean_object* v_declName_1367_){
_start:
{
lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1368_ = l_Lean_Compiler_weakSpecializeAttr;
v___x_1369_ = l_Lean_TagAttribute_hasTag(v___x_1368_, v_env_1366_, v_declName_1367_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasWeakSpecializeAttribute___boxed(lean_object* v_env_1370_, lean_object* v_declName_1371_){
_start:
{
uint8_t v_res_1372_; lean_object* v_r_1373_; 
v_res_1372_ = l_Lean_Compiler_hasWeakSpecializeAttribute(v_env_1370_, v_declName_1371_);
v_r_1373_ = lean_box(v_res_1372_);
return v_r_1373_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_Specialize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_instInhabitedSpecializeAttributeKind_default = _init_l_Lean_Compiler_instInhabitedSpecializeAttributeKind_default();
l_Lean_Compiler_instInhabitedSpecializeAttributeKind = _init_l_Lean_Compiler_instInhabitedSpecializeAttributeKind();
res = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_nospecializeAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_nospecializeAttr);
lean_dec_ref(res);
res = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_weakSpecializeAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_weakSpecializeAttr);
lean_dec_ref(res);
res = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_specializeAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_specializeAttr);
lean_dec_ref(res);
res = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3();
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
