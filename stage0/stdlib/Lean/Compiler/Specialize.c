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
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___redArg(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorIdx___impl___boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "Marks a definition to never be specialized during code generation."};
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
static const lean_string_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 299, .m_capacity = 299, .m_length = 298, .m_data = "Marks a type for weak specialization: Parameters of this type are only specialized when\nanother argument already triggers specialization. Unlike `@[nospecialize]`, if specialization\nhappens for other reasons, parameters of this type will participate in the specialization\nrather than being ignored."};
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
static const lean_array_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
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
static const lean_string_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 749, .m_capacity = 749, .m_length = 748, .m_data = "Marks a definition to always be specialized during code generation.\n\nSpecialization is an optimization in the code generator for generating variants of a function that\nare specialized to specific parameter values. This is in particular useful for functions that take\nother functions as parameters: Usually when passing functions as parameters, a closure needs to be\nallocated that will then be called. Using `@[specialize]` prevents both of these operations by\nusing the provided function directly in the specialization of the inner function.\n\n`@[specialize]` can take additional arguments for the parameter names or indices (starting at 1) of\nthe parameters that should be specialized. By default, instance and function parameters are\nspecialized."};
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
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Compiler_SpecializeAttributeKind_ctorIdx___impl(v_x_4__boxed_5_);
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
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_52_ = lean_box(v_x_50_);
v___x_53_ = lean_obj_tag_nat(v___x_52_);
lean_dec(v___x_52_);
v___x_54_ = lean_box(v_y_51_);
v___x_55_ = lean_obj_tag_nat(v___x_54_);
lean_dec(v___x_54_);
v___x_56_ = lean_nat_dec_eq(v___x_53_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_instBEqSpecializeAttributeKind_beq___boxed(lean_object* v_x_57_, lean_object* v_y_58_){
_start:
{
uint8_t v_x_24__boxed_59_; uint8_t v_y_25__boxed_60_; uint8_t v_res_61_; lean_object* v_r_62_; 
v_x_24__boxed_59_ = lean_unbox(v_x_57_);
v_y_25__boxed_60_ = lean_unbox(v_y_58_);
v_res_61_ = l_Lean_Compiler_instBEqSpecializeAttributeKind_beq(v_x_24__boxed_59_, v_y_25__boxed_60_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_(lean_object* v_x_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_box(0);
v___x_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2____boxed(lean_object* v_x_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_(v_x_71_, v___y_72_, v___y_73_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
lean_dec(v_x_71_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; 
v___f_89_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_90_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_91_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_92_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_93_ = 0;
v___x_94_ = lean_box(2);
v___x_95_ = 0;
v___x_96_ = l_Lean_registerTagAttribute(v___x_90_, v___x_91_, v___f_89_, v___x_92_, v___x_93_, v___x_94_, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2____boxed(lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_();
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1(){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_102_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1___closed__0));
v___x_103_ = l_Lean_addBuiltinDocString(v___x_101_, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1___boxed(lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1();
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3(){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_133_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__6));
v___x_134_ = l_Lean_addBuiltinDeclarationRanges(v___x_132_, v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___boxed(lean_object* v_a_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3();
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; lean_object* v___x_154_; 
v___f_147_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_148_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_));
v___x_149_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_));
v___x_150_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_));
v___x_151_ = 0;
v___x_152_ = lean_box(2);
v___x_153_ = 0;
v___x_154_ = l_Lean_registerTagAttribute(v___x_148_, v___x_149_, v___f_147_, v___x_150_, v___x_151_, v___x_152_, v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2____boxed(lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_();
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1(){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_));
v___x_160_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1___closed__0));
v___x_161_ = l_Lean_addBuiltinDocString(v___x_159_, v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1___boxed(lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1();
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3(){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_));
v___x_191_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__6));
v___x_192_ = l_Lean_addBuiltinDeclarationRanges(v___x_190_, v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___boxed(lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3();
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0(lean_object* v_k_195_, lean_object* v_b_196_, lean_object* v_c_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v___x_203_; 
lean_inc(v___y_201_);
lean_inc_ref(v___y_200_);
lean_inc(v___y_199_);
lean_inc_ref(v___y_198_);
v___x_203_ = lean_apply_7(v_k_195_, v_b_196_, v_c_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, lean_box(0));
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0___boxed(lean_object* v_k_204_, lean_object* v_b_205_, lean_object* v_c_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0(v_k_204_, v_b_205_, v_c_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(lean_object* v_type_213_, lean_object* v_k_214_, uint8_t v_cleanupAnnotations_215_, uint8_t v_whnfType_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v___f_222_; lean_object* v___x_223_; 
v___f_222_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_222_, 0, v_k_214_);
v___x_223_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_213_, v___f_222_, v_cleanupAnnotations_215_, v_whnfType_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v___x_223_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_223_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
v_a_232_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_223_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_223_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___boxed(lean_object* v_type_240_, lean_object* v_k_241_, lean_object* v_cleanupAnnotations_242_, lean_object* v_whnfType_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_249_; uint8_t v_whnfType_boxed_250_; lean_object* v_res_251_; 
v_cleanupAnnotations_boxed_249_ = lean_unbox(v_cleanupAnnotations_242_);
v_whnfType_boxed_250_ = lean_unbox(v_whnfType_243_);
v_res_251_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(v_type_240_, v_k_241_, v_cleanupAnnotations_boxed_249_, v_whnfType_boxed_250_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7(lean_object* v_00_u03b1_252_, lean_object* v_type_253_, lean_object* v_k_254_, uint8_t v_cleanupAnnotations_255_, uint8_t v_whnfType_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(v_type_253_, v_k_254_, v_cleanupAnnotations_255_, v_whnfType_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___boxed(lean_object* v_00_u03b1_263_, lean_object* v_type_264_, lean_object* v_k_265_, lean_object* v_cleanupAnnotations_266_, lean_object* v_whnfType_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_273_; uint8_t v_whnfType_boxed_274_; lean_object* v_res_275_; 
v_cleanupAnnotations_boxed_273_ = lean_unbox(v_cleanupAnnotations_266_);
v_whnfType_boxed_274_ = lean_unbox(v_whnfType_267_);
v_res_275_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7(v_00_u03b1_263_, v_type_264_, v_k_265_, v_cleanupAnnotations_boxed_273_, v_whnfType_boxed_274_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___redArg(lean_object* v_hi_276_, lean_object* v_pivot_277_, lean_object* v_as_278_, lean_object* v_i_279_, lean_object* v_k_280_){
_start:
{
uint8_t v___x_281_; 
v___x_281_ = lean_nat_dec_lt(v_k_280_, v_hi_276_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec(v_k_280_);
v___x_282_ = lean_array_fswap(v_as_278_, v_i_279_, v_hi_276_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v_i_279_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
return v___x_283_;
}
else
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = lean_array_fget_borrowed(v_as_278_, v_k_280_);
v___x_285_ = lean_nat_dec_lt(v___x_284_, v_pivot_277_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_nat_add(v_k_280_, v___x_286_);
lean_dec(v_k_280_);
v_k_280_ = v___x_287_;
goto _start;
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_289_ = lean_array_fswap(v_as_278_, v_i_279_, v_k_280_);
v___x_290_ = lean_unsigned_to_nat(1u);
v___x_291_ = lean_nat_add(v_i_279_, v___x_290_);
lean_dec(v_i_279_);
v___x_292_ = lean_nat_add(v_k_280_, v___x_290_);
lean_dec(v_k_280_);
v_as_278_ = v___x_289_;
v_i_279_ = v___x_291_;
v_k_280_ = v___x_292_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___redArg___boxed(lean_object* v_hi_294_, lean_object* v_pivot_295_, lean_object* v_as_296_, lean_object* v_i_297_, lean_object* v_k_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___redArg(v_hi_294_, v_pivot_295_, v_as_296_, v_i_297_, v_k_298_);
lean_dec(v_pivot_295_);
lean_dec(v_hi_294_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(lean_object* v_n_300_, lean_object* v_as_301_, lean_object* v_lo_302_, lean_object* v_hi_303_){
_start:
{
lean_object* v___y_305_; uint8_t v___x_315_; 
v___x_315_ = lean_nat_dec_lt(v_lo_302_, v_hi_303_);
if (v___x_315_ == 0)
{
lean_dec(v_lo_302_);
return v_as_301_;
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v_mid_318_; lean_object* v___y_320_; lean_object* v___y_326_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_316_ = lean_nat_add(v_lo_302_, v_hi_303_);
v___x_317_ = lean_unsigned_to_nat(1u);
v_mid_318_ = lean_nat_shiftr(v___x_316_, v___x_317_);
lean_dec(v___x_316_);
v___x_331_ = lean_array_fget_borrowed(v_as_301_, v_mid_318_);
v___x_332_ = lean_array_fget_borrowed(v_as_301_, v_lo_302_);
v___x_333_ = lean_nat_dec_lt(v___x_331_, v___x_332_);
if (v___x_333_ == 0)
{
v___y_326_ = v_as_301_;
goto v___jp_325_;
}
else
{
lean_object* v___x_334_; 
v___x_334_ = lean_array_fswap(v_as_301_, v_lo_302_, v_mid_318_);
v___y_326_ = v___x_334_;
goto v___jp_325_;
}
v___jp_319_:
{
lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_321_ = lean_array_fget_borrowed(v___y_320_, v_mid_318_);
v___x_322_ = lean_array_fget_borrowed(v___y_320_, v_hi_303_);
v___x_323_ = lean_nat_dec_lt(v___x_321_, v___x_322_);
if (v___x_323_ == 0)
{
lean_dec(v_mid_318_);
v___y_305_ = v___y_320_;
goto v___jp_304_;
}
else
{
lean_object* v___x_324_; 
v___x_324_ = lean_array_fswap(v___y_320_, v_mid_318_, v_hi_303_);
lean_dec(v_mid_318_);
v___y_305_ = v___x_324_;
goto v___jp_304_;
}
}
v___jp_325_:
{
lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_327_ = lean_array_fget_borrowed(v___y_326_, v_hi_303_);
v___x_328_ = lean_array_fget_borrowed(v___y_326_, v_lo_302_);
v___x_329_ = lean_nat_dec_lt(v___x_327_, v___x_328_);
if (v___x_329_ == 0)
{
v___y_320_ = v___y_326_;
goto v___jp_319_;
}
else
{
lean_object* v___x_330_; 
v___x_330_ = lean_array_fswap(v___y_326_, v_lo_302_, v_hi_303_);
v___y_320_ = v___x_330_;
goto v___jp_319_;
}
}
}
v___jp_304_:
{
lean_object* v_pivot_306_; lean_object* v___x_307_; lean_object* v_fst_308_; lean_object* v_snd_309_; uint8_t v___x_310_; 
v_pivot_306_ = lean_array_fget(v___y_305_, v_hi_303_);
lean_inc_n(v_lo_302_, 2);
v___x_307_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___redArg(v_hi_303_, v_pivot_306_, v___y_305_, v_lo_302_, v_lo_302_);
lean_dec(v_pivot_306_);
v_fst_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_fst_308_);
v_snd_309_ = lean_ctor_get(v___x_307_, 1);
lean_inc(v_snd_309_);
lean_dec_ref(v___x_307_);
v___x_310_ = lean_nat_dec_le(v_hi_303_, v_fst_308_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(v_n_300_, v_snd_309_, v_lo_302_, v_fst_308_);
v___x_312_ = lean_unsigned_to_nat(1u);
v___x_313_ = lean_nat_add(v_fst_308_, v___x_312_);
lean_dec(v_fst_308_);
v_as_301_ = v___x_311_;
v_lo_302_ = v___x_313_;
goto _start;
}
else
{
lean_dec(v_fst_308_);
lean_dec(v_lo_302_);
return v_snd_309_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg___boxed(lean_object* v_n_335_, lean_object* v_as_336_, lean_object* v_lo_337_, lean_object* v_hi_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(v_n_335_, v_as_336_, v_lo_337_, v_hi_338_);
lean_dec(v_hi_338_);
lean_dec(v_n_335_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg(size_t v_sz_340_, size_t v_i_341_, lean_object* v_bs_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
uint8_t v___x_347_; 
v___x_347_ = lean_usize_dec_lt(v_i_341_, v_sz_340_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; 
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v_bs_342_);
return v___x_348_;
}
else
{
lean_object* v_v_349_; lean_object* v___x_350_; lean_object* v_bs_x27_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v_v_349_ = lean_array_uget(v_bs_342_, v_i_341_);
v___x_350_ = lean_unsigned_to_nat(0u);
v_bs_x27_351_ = lean_array_uset(v_bs_342_, v_i_341_, v___x_350_);
v___x_352_ = l_Lean_Expr_fvarId_x21(v_v_349_);
lean_dec(v_v_349_);
v___x_353_ = l_Lean_FVarId_getUserName___redArg(v___x_352_, v___y_343_, v___y_344_, v___y_345_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; size_t v___x_355_; size_t v___x_356_; lean_object* v___x_357_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_a_354_);
lean_dec_ref_known(v___x_353_, 1);
v___x_355_ = ((size_t)1ULL);
v___x_356_ = lean_usize_add(v_i_341_, v___x_355_);
v___x_357_ = lean_array_uset(v_bs_x27_351_, v_i_341_, v_a_354_);
v_i_341_ = v___x_356_;
v_bs_342_ = v___x_357_;
goto _start;
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec_ref(v_bs_x27_351_);
v_a_359_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_353_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_353_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg___boxed(lean_object* v_sz_367_, lean_object* v_i_368_, lean_object* v_bs_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
size_t v_sz_boxed_374_; size_t v_i_boxed_375_; lean_object* v_res_376_; 
v_sz_boxed_374_ = lean_unbox_usize(v_sz_367_);
lean_dec(v_sz_367_);
v_i_boxed_375_ = lean_unbox_usize(v_i_368_);
lean_dec(v_i_368_);
v_res_376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg(v_sz_boxed_374_, v_i_boxed_375_, v_bs_369_, v___y_370_, v___y_371_, v___y_372_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec_ref(v___y_370_);
return v_res_376_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1(lean_object* v_a_377_, lean_object* v_as_378_, size_t v_i_379_, size_t v_stop_380_){
_start:
{
uint8_t v___x_381_; 
v___x_381_ = lean_usize_dec_eq(v_i_379_, v_stop_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_382_ = lean_array_uget_borrowed(v_as_378_, v_i_379_);
v___x_383_ = lean_nat_dec_eq(v_a_377_, v___x_382_);
if (v___x_383_ == 0)
{
size_t v___x_384_; size_t v___x_385_; 
v___x_384_ = ((size_t)1ULL);
v___x_385_ = lean_usize_add(v_i_379_, v___x_384_);
v_i_379_ = v___x_385_;
goto _start;
}
else
{
return v___x_383_;
}
}
else
{
uint8_t v___x_387_; 
v___x_387_ = 0;
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1___boxed(lean_object* v_a_388_, lean_object* v_as_389_, lean_object* v_i_390_, lean_object* v_stop_391_){
_start:
{
size_t v_i_boxed_392_; size_t v_stop_boxed_393_; uint8_t v_res_394_; lean_object* v_r_395_; 
v_i_boxed_392_ = lean_unbox_usize(v_i_390_);
lean_dec(v_i_390_);
v_stop_boxed_393_ = lean_unbox_usize(v_stop_391_);
lean_dec(v_stop_391_);
v_res_394_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1(v_a_388_, v_as_389_, v_i_boxed_392_, v_stop_boxed_393_);
lean_dec_ref(v_as_389_);
lean_dec(v_a_388_);
v_r_395_ = lean_box(v_res_394_);
return v_r_395_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1(lean_object* v_as_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_398_ = lean_unsigned_to_nat(0u);
v___x_399_ = lean_array_get_size(v_as_396_);
v___x_400_ = lean_nat_dec_lt(v___x_398_, v___x_399_);
if (v___x_400_ == 0)
{
return v___x_400_;
}
else
{
if (v___x_400_ == 0)
{
return v___x_400_;
}
else
{
size_t v___x_401_; size_t v___x_402_; uint8_t v___x_403_; 
v___x_401_ = ((size_t)0ULL);
v___x_402_ = lean_usize_of_nat(v___x_399_);
v___x_403_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1(v_a_397_, v_as_396_, v___x_401_, v___x_402_);
return v___x_403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1___boxed(lean_object* v_as_404_, lean_object* v_a_405_){
_start:
{
uint8_t v_res_406_; lean_object* v_r_407_; 
v_res_406_ = l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1(v_as_404_, v_a_405_);
lean_dec(v_a_405_);
lean_dec_ref(v_as_404_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5_spec__8(lean_object* v_xs_408_, lean_object* v_v_409_, lean_object* v_i_410_){
_start:
{
lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_411_ = lean_array_get_size(v_xs_408_);
v___x_412_ = lean_nat_dec_lt(v_i_410_, v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; 
lean_dec(v_i_410_);
v___x_413_ = lean_box(0);
return v___x_413_;
}
else
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = lean_array_fget_borrowed(v_xs_408_, v_i_410_);
v___x_415_ = lean_name_eq(v___x_414_, v_v_409_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_unsigned_to_nat(1u);
v___x_417_ = lean_nat_add(v_i_410_, v___x_416_);
lean_dec(v_i_410_);
v_i_410_ = v___x_417_;
goto _start;
}
else
{
lean_object* v___x_419_; 
v___x_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_419_, 0, v_i_410_);
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_420_, lean_object* v_v_421_, lean_object* v_i_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5_spec__8(v_xs_420_, v_v_421_, v_i_422_);
lean_dec(v_v_421_);
lean_dec_ref(v_xs_420_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5(lean_object* v_xs_424_, lean_object* v_v_425_){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5_spec__8(v_xs_424_, v_v_425_, v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5___boxed(lean_object* v_xs_428_, lean_object* v_v_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5(v_xs_428_, v_v_429_);
lean_dec(v_v_429_);
lean_dec_ref(v_xs_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3(lean_object* v_xs_431_, lean_object* v_v_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5(v_xs_431_, v_v_432_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v___x_434_; 
v___x_434_ = lean_box(0);
return v___x_434_;
}
else
{
lean_object* v_val_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
v_val_435_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_442_ == 0)
{
v___x_437_ = v___x_433_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_val_435_);
lean_dec(v___x_433_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_val_435_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3___boxed(lean_object* v_xs_443_, lean_object* v_v_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3(v_xs_443_, v_v_444_);
lean_dec(v_v_444_);
lean_dec_ref(v_xs_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5(lean_object* v_msgData_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v___x_452_; lean_object* v_env_453_; uint8_t v___x_454_; lean_object* v_env_455_; lean_object* v___x_456_; lean_object* v_toCold_457_; lean_object* v_mctx_458_; lean_object* v_lctx_459_; lean_object* v_options_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_452_ = lean_st_ref_get(v___y_450_);
v_env_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc_ref(v_env_453_);
lean_dec(v___x_452_);
v___x_454_ = 0;
v_env_455_ = l_Lean_Environment_setRecordingDeps(v_env_453_, v___x_454_);
v___x_456_ = lean_st_ref_get(v___y_448_);
v_toCold_457_ = lean_ctor_get(v___y_449_, 0);
v_mctx_458_ = lean_ctor_get(v___x_456_, 0);
lean_inc_ref(v_mctx_458_);
lean_dec(v___x_456_);
v_lctx_459_ = lean_ctor_get(v___y_447_, 2);
v_options_460_ = lean_ctor_get(v_toCold_457_, 2);
lean_inc_ref(v_options_460_);
lean_inc_ref(v_lctx_459_);
v___x_461_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_461_, 0, v_env_455_);
lean_ctor_set(v___x_461_, 1, v_mctx_458_);
lean_ctor_set(v___x_461_, 2, v_lctx_459_);
lean_ctor_set(v___x_461_, 3, v_options_460_);
v___x_462_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v_msgData_446_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5___boxed(lean_object* v_msgData_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5(v_msgData_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg(lean_object* v_msg_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_ref_477_; lean_object* v___x_478_; lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_487_; 
v_ref_477_ = lean_ctor_get(v___y_474_, 2);
v___x_478_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5(v_msg_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_487_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_485_; 
lean_inc(v_ref_477_);
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v_ref_477_);
lean_ctor_set(v___x_483_, 1, v_a_479_);
if (v_isShared_482_ == 0)
{
lean_ctor_set_tag(v___x_481_, 1);
lean_ctor_set(v___x_481_, 0, v___x_483_);
v___x_485_ = v___x_481_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg___boxed(lean_object* v_msg_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg(v_msg_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(lean_object* v_ref_495_, lean_object* v_msg_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_toCold_502_; lean_object* v_currRecDepth_503_; lean_object* v_ref_504_; uint16_t v_optionFlags_505_; uint8_t v_suppressElabErrors_506_; uint8_t v_isRecordingDeps_507_; lean_object* v_ref_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v_toCold_502_ = lean_ctor_get(v___y_499_, 0);
v_currRecDepth_503_ = lean_ctor_get(v___y_499_, 1);
v_ref_504_ = lean_ctor_get(v___y_499_, 2);
v_optionFlags_505_ = lean_ctor_get_uint16(v___y_499_, sizeof(void*)*3);
v_suppressElabErrors_506_ = lean_ctor_get_uint8(v___y_499_, sizeof(void*)*3 + 2);
v_isRecordingDeps_507_ = lean_ctor_get_uint8(v___y_499_, sizeof(void*)*3 + 3);
v_ref_508_ = l_Lean_replaceRef(v_ref_495_, v_ref_504_);
lean_inc(v_currRecDepth_503_);
lean_inc_ref(v_toCold_502_);
v___x_509_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_509_, 0, v_toCold_502_);
lean_ctor_set(v___x_509_, 1, v_currRecDepth_503_);
lean_ctor_set(v___x_509_, 2, v_ref_508_);
lean_ctor_set_uint16(v___x_509_, sizeof(void*)*3, v_optionFlags_505_);
lean_ctor_set_uint8(v___x_509_, sizeof(void*)*3 + 2, v_suppressElabErrors_506_);
lean_ctor_set_uint8(v___x_509_, sizeof(void*)*3 + 3, v_isRecordingDeps_507_);
v___x_510_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg(v_msg_496_, v___y_497_, v___y_498_, v___x_509_, v___y_500_);
lean_dec_ref_known(v___x_509_, 3);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg___boxed(lean_object* v_ref_511_, lean_object* v_msg_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_ref_511_, v_msg_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v_ref_511_);
return v_res_518_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__0));
v___x_521_ = l_Lean_stringToMessageData(v___x_520_);
return v___x_521_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__2));
v___x_524_ = l_Lean_stringToMessageData(v___x_523_);
return v___x_524_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__4));
v___x_527_ = l_Lean_stringToMessageData(v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__6));
v___x_530_ = l_Lean_stringToMessageData(v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__8));
v___x_533_ = l_Lean_stringToMessageData(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__10));
v___x_536_ = l_Lean_stringToMessageData(v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__12));
v___x_539_ = l_Lean_stringToMessageData(v___x_538_);
return v___x_539_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__14));
v___x_542_ = l_Lean_stringToMessageData(v___x_541_);
return v___x_542_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__16));
v___x_545_ = l_Lean_stringToMessageData(v___x_544_);
return v___x_545_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__18));
v___x_548_ = l_Lean_stringToMessageData(v___x_547_);
return v___x_548_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__20));
v___x_551_ = l_Lean_stringToMessageData(v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4(lean_object* v_a_552_, lean_object* v_declName_553_, lean_object* v___x_554_, lean_object* v_as_555_, size_t v_sz_556_, size_t v_i_557_, lean_object* v_b_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_a_565_; lean_object* v___y_570_; uint8_t v___x_572_; 
v___x_572_ = lean_usize_dec_lt(v_i_557_, v_sz_556_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; 
lean_dec(v_declName_553_);
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v_b_558_);
return v___x_573_;
}
else
{
lean_object* v___x_574_; uint8_t v___x_575_; lean_object* v_a_576_; lean_object* v___x_577_; 
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = lean_nat_dec_eq(v___x_554_, v___x_574_);
v_a_576_ = lean_array_uget_borrowed(v_as_555_, v_i_557_);
v___x_577_ = l_Lean_Syntax_isNatLit_x3f(v_a_576_);
if (lean_obj_tag(v___x_577_) == 1)
{
lean_object* v_val_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_655_; 
v_val_578_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_655_ == 0)
{
v___x_580_ = v___x_577_;
v_isShared_581_ = v_isSharedCheck_655_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_val_578_);
lean_dec(v___x_577_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_655_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; uint8_t v___x_644_; 
v___x_644_ = lean_nat_dec_eq(v_val_578_, v___x_574_);
if (v___x_644_ == 0)
{
v___y_583_ = v___y_559_;
v___y_584_ = v___y_560_;
v___y_585_ = v___y_561_;
v___y_586_ = v___y_562_;
goto v___jp_582_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15);
v___x_646_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_576_, v___x_645_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_dec_ref_known(v___x_646_, 1);
v___y_583_ = v___y_559_;
v___y_584_ = v___y_560_;
v___y_585_ = v___y_561_;
v___y_586_ = v___y_562_;
goto v___jp_582_;
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_del_object(v___x_580_);
lean_dec(v_val_578_);
lean_dec_ref(v_b_558_);
lean_dec(v_declName_553_);
v_a_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
v___jp_582_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_587_ = lean_unsigned_to_nat(1u);
v___x_588_ = lean_nat_sub(v_val_578_, v___x_587_);
lean_dec(v_val_578_);
v___x_589_ = lean_array_get_size(v_a_552_);
v___x_590_ = lean_nat_dec_le(v___x_589_, v___x_588_);
if (v___x_590_ == 0)
{
uint8_t v___x_591_; 
v___x_591_ = l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1(v_b_558_, v___x_588_);
if (v___x_591_ == 0)
{
lean_del_object(v___x_580_);
v___y_570_ = v___x_588_;
goto v___jp_569_;
}
else
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_592_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1);
v___x_593_ = lean_nat_add(v___x_588_, v___x_587_);
v___x_594_ = l_Nat_reprFast(v___x_593_);
if (v_isShared_581_ == 0)
{
lean_ctor_set_tag(v___x_580_, 3);
lean_ctor_set(v___x_580_, 0, v___x_594_);
v___x_596_ = v___x_580_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_594_);
v___x_596_ = v_reuseFailAlloc_615_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_597_ = l_Lean_MessageData_ofFormat(v___x_596_);
v___x_598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_592_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3);
v___x_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_array_fget_borrowed(v_a_552_, v___x_588_);
lean_inc(v___x_601_);
v___x_602_ = l_Lean_MessageData_ofName(v___x_601_);
v___x_603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_600_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5);
v___x_605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_576_, v___x_605_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_dec_ref_known(v___x_606_, 1);
v___y_570_ = v___x_588_;
goto v___jp_569_;
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec(v___x_588_);
lean_dec_ref(v_b_558_);
lean_dec(v_declName_553_);
v_a_607_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_606_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_616_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7);
v___x_617_ = l_Nat_reprFast(v___x_588_);
if (v_isShared_581_ == 0)
{
lean_ctor_set_tag(v___x_580_, 3);
lean_ctor_set(v___x_580_, 0, v___x_617_);
v___x_619_ = v___x_580_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_617_);
v___x_619_ = v_reuseFailAlloc_643_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_620_ = l_Lean_MessageData_ofFormat(v___x_619_);
v___x_621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_616_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9);
v___x_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
lean_inc(v_declName_553_);
v___x_624_ = l_Lean_MessageData_ofConstName(v_declName_553_, v___x_575_);
v___x_625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11);
v___x_627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = l_Nat_reprFast(v___x_589_);
v___x_629_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
v___x_630_ = l_Lean_MessageData_ofFormat(v___x_629_);
v___x_631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_627_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13);
v___x_633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_631_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_576_, v___x_633_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_dec_ref_known(v___x_634_, 1);
v_a_565_ = v_b_558_;
goto v___jp_564_;
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
lean_dec_ref(v_b_558_);
lean_dec(v_declName_553_);
v_a_635_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_634_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
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
lean_object* v___x_656_; lean_object* v___x_657_; 
lean_dec(v___x_577_);
v___x_656_ = l_Lean_Syntax_getId(v_a_576_);
v___x_657_ = l_Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3(v_a_552_, v___x_656_);
if (lean_obj_tag(v___x_657_) == 1)
{
lean_object* v_val_658_; uint8_t v___x_661_; 
v_val_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_val_658_);
lean_dec_ref_known(v___x_657_, 1);
v___x_661_ = l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1(v_b_558_, v_val_658_);
if (v___x_661_ == 0)
{
lean_dec(v___x_656_);
goto v___jp_659_;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_662_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17);
v___x_663_ = l_Lean_MessageData_ofName(v___x_656_);
v___x_664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_662_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19);
v___x_666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_664_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_576_, v___x_666_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_dec_ref_known(v___x_667_, 1);
goto v___jp_659_;
}
else
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
lean_dec(v_val_658_);
lean_dec_ref(v_b_558_);
lean_dec(v_declName_553_);
v_a_668_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_667_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
v___jp_659_:
{
lean_object* v___x_660_; 
v___x_660_ = lean_array_push(v_b_558_, v_val_658_);
v_a_565_ = v___x_660_;
goto v___jp_564_;
}
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
lean_dec(v___x_657_);
v___x_676_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17);
v___x_677_ = l_Lean_MessageData_ofName(v___x_656_);
v___x_678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_676_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9);
v___x_680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_678_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
lean_inc(v_declName_553_);
v___x_681_ = l_Lean_MessageData_ofConstName(v_declName_553_, v___x_575_);
v___x_682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_680_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21);
v___x_684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_682_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_576_, v___x_684_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_dec_ref_known(v___x_685_, 1);
v_a_565_ = v_b_558_;
goto v___jp_564_;
}
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
lean_dec_ref(v_b_558_);
lean_dec(v_declName_553_);
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
}
v___jp_564_:
{
size_t v___x_566_; size_t v___x_567_; 
v___x_566_ = ((size_t)1ULL);
v___x_567_ = lean_usize_add(v_i_557_, v___x_566_);
v_i_557_ = v___x_567_;
v_b_558_ = v_a_565_;
goto _start;
}
v___jp_569_:
{
lean_object* v___x_571_; 
v___x_571_ = lean_array_push(v_b_558_, v___y_570_);
v_a_565_ = v___x_571_;
goto v___jp_564_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___boxed(lean_object* v_a_694_, lean_object* v_declName_695_, lean_object* v___x_696_, lean_object* v_as_697_, lean_object* v_sz_698_, lean_object* v_i_699_, lean_object* v_b_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
size_t v_sz_boxed_706_; size_t v_i_boxed_707_; lean_object* v_res_708_; 
v_sz_boxed_706_ = lean_unbox_usize(v_sz_698_);
lean_dec(v_sz_698_);
v_i_boxed_707_ = lean_unbox_usize(v_i_699_);
lean_dec(v_i_699_);
v_res_708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4(v_a_694_, v_declName_695_, v___x_696_, v_as_697_, v_sz_boxed_706_, v_i_boxed_707_, v_b_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec_ref(v_as_697_);
lean_dec(v___x_696_);
lean_dec_ref(v_a_694_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0(lean_object* v___x_709_, lean_object* v_args_710_, lean_object* v_declName_711_, lean_object* v___x_712_, lean_object* v_xs_713_, lean_object* v_x_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
size_t v_sz_720_; size_t v___x_721_; lean_object* v___x_722_; 
v_sz_720_ = lean_array_size(v_xs_713_);
v___x_721_ = ((size_t)0ULL);
v___x_722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg(v_sz_720_, v___x_721_, v_xs_713_, v___y_715_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_746_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_746_ == 0)
{
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_746_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_746_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; size_t v_sz_728_; lean_object* v___x_729_; 
v___x_727_ = lean_mk_empty_array_with_capacity(v___x_709_);
v_sz_728_ = lean_array_size(v_args_710_);
v___x_729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4(v_a_723_, v_declName_711_, v___x_712_, v_args_710_, v_sz_728_, v___x_721_, v___x_727_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
lean_dec(v_a_723_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_731_; lean_object* v___y_733_; lean_object* v___y_734_; uint8_t v___x_739_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
v___x_731_ = lean_array_get_size(v_a_730_);
v___x_739_ = lean_nat_dec_eq(v___x_731_, v___x_709_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___y_743_; uint8_t v___x_745_; 
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_729_, 1);
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = lean_nat_sub(v___x_731_, v___x_740_);
v___x_745_ = lean_nat_dec_le(v___x_709_, v___x_741_);
if (v___x_745_ == 0)
{
lean_dec(v___x_709_);
lean_inc(v___x_741_);
v___y_743_ = v___x_741_;
goto v___jp_742_;
}
else
{
v___y_743_ = v___x_709_;
goto v___jp_742_;
}
v___jp_742_:
{
uint8_t v___x_744_; 
v___x_744_ = lean_nat_dec_le(v___y_743_, v___x_741_);
if (v___x_744_ == 0)
{
lean_dec(v___x_741_);
lean_inc(v___y_743_);
v___y_733_ = v___y_743_;
v___y_734_ = v___y_743_;
goto v___jp_732_;
}
else
{
v___y_733_ = v___y_743_;
v___y_734_ = v___x_741_;
goto v___jp_732_;
}
}
}
else
{
lean_del_object(v___x_725_);
lean_dec(v___x_709_);
return v___x_729_;
}
v___jp_732_:
{
lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_735_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(v___x_731_, v_a_730_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v___x_735_);
v___x_737_ = v___x_725_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
else
{
lean_del_object(v___x_725_);
lean_dec(v___x_709_);
return v___x_729_;
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec(v_declName_711_);
lean_dec(v___x_709_);
v_a_747_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_722_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_722_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0___boxed(lean_object* v___x_755_, lean_object* v_args_756_, lean_object* v_declName_757_, lean_object* v___x_758_, lean_object* v_xs_759_, lean_object* v_x_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0(v___x_755_, v_args_756_, v_declName_757_, v___x_758_, v_xs_759_, v_x_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec_ref(v_x_760_);
lean_dec(v___x_758_);
lean_dec_ref(v_args_756_);
return v_res_766_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0(void){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_767_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0);
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
return v___x_769_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__2(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_770_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1);
v___x_771_ = lean_unsigned_to_nat(0u);
v___x_772_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
lean_ctor_set(v___x_772_, 2, v___x_771_);
lean_ctor_set(v___x_772_, 3, v___x_771_);
lean_ctor_set(v___x_772_, 4, v___x_770_);
lean_ctor_set(v___x_772_, 5, v___x_770_);
lean_ctor_set(v___x_772_, 6, v___x_770_);
lean_ctor_set(v___x_772_, 7, v___x_770_);
lean_ctor_set(v___x_772_, 8, v___x_770_);
lean_ctor_set(v___x_772_, 9, v___x_770_);
lean_ctor_set(v___x_772_, 10, v___x_770_);
return v___x_772_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_773_ = lean_unsigned_to_nat(32u);
v___x_774_ = lean_mk_empty_array_with_capacity(v___x_773_);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
return v___x_775_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4(void){
_start:
{
size_t v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_776_ = ((size_t)5ULL);
v___x_777_ = lean_unsigned_to_nat(0u);
v___x_778_ = lean_unsigned_to_nat(32u);
v___x_779_ = lean_mk_empty_array_with_capacity(v___x_778_);
v___x_780_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__3);
v___x_781_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v___x_779_);
lean_ctor_set(v___x_781_, 2, v___x_777_);
lean_ctor_set(v___x_781_, 3, v___x_777_);
lean_ctor_set_usize(v___x_781_, 4, v___x_776_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__5(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_782_ = lean_box(1);
v___x_783_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4);
v___x_784_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1);
v___x_785_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
lean_ctor_set(v___x_785_, 1, v___x_783_);
lean_ctor_set(v___x_785_, 2, v___x_782_);
return v___x_785_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__6));
v___x_788_ = l_Lean_stringToMessageData(v___x_787_);
return v___x_788_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__9(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__8));
v___x_791_ = l_Lean_stringToMessageData(v___x_790_);
return v___x_791_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__11(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__10));
v___x_794_ = l_Lean_stringToMessageData(v___x_793_);
return v___x_794_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__13(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__12));
v___x_797_ = l_Lean_stringToMessageData(v___x_796_);
return v___x_797_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__15(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__14));
v___x_800_ = l_Lean_stringToMessageData(v___x_799_);
return v___x_800_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__17(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__16));
v___x_803_ = l_Lean_stringToMessageData(v___x_802_);
return v___x_803_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__19(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__18));
v___x_806_ = l_Lean_stringToMessageData(v___x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg(lean_object* v_msg_807_, lean_object* v_declHint_808_, lean_object* v___y_809_){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v_env_813_; uint8_t v___x_814_; 
v___x_811_ = lean_box(0);
v___x_812_ = lean_st_ref_get(v___y_809_);
v_env_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc_ref(v_env_813_);
lean_dec(v___x_812_);
v___x_814_ = l_Lean_Name_isAnonymous(v_declHint_808_);
if (v___x_814_ == 0)
{
uint8_t v_isExporting_815_; 
v_isExporting_815_ = lean_ctor_get_uint8(v_env_813_, sizeof(void*)*13);
if (v_isExporting_815_ == 0)
{
lean_object* v___x_816_; 
lean_dec_ref(v_env_813_);
lean_dec(v_declHint_808_);
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v_msg_807_);
return v___x_816_;
}
else
{
lean_object* v___x_817_; uint8_t v___x_818_; 
lean_inc_ref(v_env_813_);
v___x_817_ = l_Lean_Environment_setExporting(v_env_813_, v___x_814_);
lean_inc(v_declHint_808_);
lean_inc_ref(v___x_817_);
v___x_818_ = l_Lean_Environment_contains(v___x_817_, v_declHint_808_, v_isExporting_815_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; 
lean_dec_ref(v___x_817_);
lean_dec_ref(v_env_813_);
lean_dec(v_declHint_808_);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v_msg_807_);
return v___x_819_;
}
else
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v_c_825_; lean_object* v___x_826_; 
v___x_820_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__2);
v___x_821_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__5);
v___x_822_ = l_Lean_Options_empty;
v___x_823_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_823_, 0, v___x_817_);
lean_ctor_set(v___x_823_, 1, v___x_820_);
lean_ctor_set(v___x_823_, 2, v___x_821_);
lean_ctor_set(v___x_823_, 3, v___x_822_);
lean_inc(v_declHint_808_);
v___x_824_ = l_Lean_MessageData_ofConstName(v_declHint_808_, v___x_814_);
v_c_825_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_825_, 0, v___x_823_);
lean_ctor_set(v_c_825_, 1, v___x_824_);
v___x_826_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_813_, v_declHint_808_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
lean_dec_ref(v_env_813_);
lean_dec(v_declHint_808_);
v___x_827_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7);
v___x_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v_c_825_);
v___x_829_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__9);
v___x_830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_828_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = l_Lean_MessageData_note(v___x_830_);
v___x_832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_832_, 0, v_msg_807_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
return v___x_833_;
}
else
{
lean_object* v_val_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_868_; 
v_val_834_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_868_ == 0)
{
v___x_836_ = v___x_826_;
v_isShared_837_ = v_isSharedCheck_868_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_val_834_);
lean_dec(v___x_826_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_868_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v_mod_840_; uint8_t v___x_841_; 
v___x_838_ = l_Lean_Environment_header(v_env_813_);
lean_dec_ref(v_env_813_);
v___x_839_ = l_Lean_EnvironmentHeader_moduleNames(v___x_838_);
v_mod_840_ = lean_array_get(v___x_811_, v___x_839_, v_val_834_);
lean_dec(v_val_834_);
lean_dec_ref(v___x_839_);
v___x_841_ = l_Lean_isPrivateName(v_declHint_808_);
lean_dec(v_declHint_808_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_842_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__11);
v___x_843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
lean_ctor_set(v___x_843_, 1, v_c_825_);
v___x_844_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__13);
v___x_845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_843_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = l_Lean_MessageData_ofName(v_mod_840_);
v___x_847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_845_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__15);
v___x_849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_847_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = l_Lean_MessageData_note(v___x_849_);
v___x_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_851_, 0, v_msg_807_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
if (v_isShared_837_ == 0)
{
lean_ctor_set_tag(v___x_836_, 0);
lean_ctor_set(v___x_836_, 0, v___x_851_);
v___x_853_ = v___x_836_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
else
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_855_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7);
v___x_856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v_c_825_);
v___x_857_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__17);
v___x_858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_856_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = l_Lean_MessageData_ofName(v_mod_840_);
v___x_860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_858_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__19);
v___x_862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = l_Lean_MessageData_note(v___x_862_);
v___x_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_864_, 0, v_msg_807_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
if (v_isShared_837_ == 0)
{
lean_ctor_set_tag(v___x_836_, 0);
lean_ctor_set(v___x_836_, 0, v___x_864_);
v___x_866_ = v___x_836_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_869_; 
lean_dec_ref(v_env_813_);
lean_dec(v_declHint_808_);
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v_msg_807_);
return v___x_869_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___boxed(lean_object* v_msg_870_, lean_object* v_declHint_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg(v_msg_870_, v_declHint_871_, v___y_872_);
lean_dec(v___y_872_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16(lean_object* v_msg_875_, lean_object* v_declHint_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___x_882_; lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_892_; 
v___x_882_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg(v_msg_875_, v_declHint_876_, v___y_880_);
v_a_883_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_892_ == 0)
{
v___x_885_ = v___x_882_;
v_isShared_886_ = v_isSharedCheck_892_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_882_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_892_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_887_ = l_Lean_unknownIdentifierMessageTag;
v___x_888_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set(v___x_888_, 1, v_a_883_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_888_);
v___x_890_ = v___x_885_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16___boxed(lean_object* v_msg_893_, lean_object* v_declHint_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16(v_msg_893_, v_declHint_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg(lean_object* v_ref_901_, lean_object* v_msg_902_, lean_object* v_declHint_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; lean_object* v_a_910_; lean_object* v___x_911_; 
v___x_909_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16(v_msg_902_, v_declHint_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref(v___x_909_);
v___x_911_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_ref_901_, v_a_910_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg___boxed(lean_object* v_ref_912_, lean_object* v_msg_913_, lean_object* v_declHint_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg(v_ref_912_, v_msg_913_, v_declHint_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v_ref_912_);
return v_res_920_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__1(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__0));
v___x_923_ = l_Lean_stringToMessageData(v___x_922_);
return v___x_923_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__2));
v___x_926_ = l_Lean_stringToMessageData(v___x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg(lean_object* v_ref_927_, lean_object* v_constName_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___x_934_; uint8_t v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_934_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__1);
v___x_935_ = 0;
lean_inc(v_constName_928_);
v___x_936_ = l_Lean_MessageData_ofConstName(v_constName_928_, v___x_935_);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_934_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__3);
v___x_939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_937_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg(v_ref_927_, v___x_939_, v_constName_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___boxed(lean_object* v_ref_941_, lean_object* v_constName_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg(v_ref_941_, v_constName_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v_ref_941_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg(lean_object* v_constName_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_ref_955_; lean_object* v___x_956_; 
v_ref_955_ = lean_ctor_get(v___y_952_, 2);
v___x_956_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg(v_ref_955_, v_constName_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg___boxed(lean_object* v_constName_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg(v_constName_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6(lean_object* v_constName_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___x_970_; lean_object* v_env_971_; uint8_t v___x_972_; lean_object* v___x_973_; 
v___x_970_ = lean_st_ref_get(v___y_968_);
v_env_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc_ref(v_env_971_);
lean_dec(v___x_970_);
v___x_972_ = 0;
lean_inc(v_constName_964_);
v___x_973_ = l_Lean_Environment_find_x3f(v_env_971_, v_constName_964_, v___x_972_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg(v_constName_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
return v___x_974_;
}
else
{
lean_object* v_val_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec(v_constName_964_);
v_val_975_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_973_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_val_975_);
lean_dec(v___x_973_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set_tag(v___x_977_, 0);
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_val_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6___boxed(lean_object* v_constName_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6(v_constName_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs(lean_object* v_declName_992_, lean_object* v_args_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_999_ = lean_array_get_size(v_args_993_);
v___x_1000_ = lean_unsigned_to_nat(0u);
v___x_1001_ = lean_nat_dec_eq(v___x_999_, v___x_1000_);
if (v___x_1001_ == 0)
{
lean_object* v___f_1002_; lean_object* v___x_1003_; 
lean_inc(v_declName_992_);
v___f_1002_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1002_, 0, v___x_1000_);
lean_closure_set(v___f_1002_, 1, v_args_993_);
lean_closure_set(v___f_1002_, 2, v_declName_992_);
lean_closure_set(v___f_1002_, 3, v___x_999_);
v___x_1003_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6(v_declName_992_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = l_Lean_ConstantInfo_type(v_a_1004_);
lean_dec(v_a_1004_);
v___x_1006_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(v___x_1005_, v___f_1002_, v___x_1001_, v___x_1001_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
return v___x_1006_;
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec_ref(v___f_1002_);
v_a_1007_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_1003_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1003_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
lean_dec_ref(v_args_993_);
lean_dec(v_declName_992_);
v___x_1015_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___closed__0));
v___x_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
return v___x_1016_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___boxed(lean_object* v_declName_1017_, lean_object* v_args_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs(v_declName_1017_, v_args_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0(size_t v_sz_1025_, size_t v_i_1026_, lean_object* v_bs_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg(v_sz_1025_, v_i_1026_, v_bs_1027_, v___y_1028_, v___y_1030_, v___y_1031_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___boxed(lean_object* v_sz_1034_, lean_object* v_i_1035_, lean_object* v_bs_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
size_t v_sz_boxed_1042_; size_t v_i_boxed_1043_; lean_object* v_res_1044_; 
v_sz_boxed_1042_ = lean_unbox_usize(v_sz_1034_);
lean_dec(v_sz_1034_);
v_i_boxed_1043_ = lean_unbox_usize(v_i_1035_);
lean_dec(v_i_1035_);
v_res_1044_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0(v_sz_boxed_1042_, v_i_boxed_1043_, v_bs_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2(lean_object* v_00_u03b1_1045_, lean_object* v_ref_1046_, lean_object* v_msg_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_ref_1046_, v_msg_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___boxed(lean_object* v_00_u03b1_1054_, lean_object* v_ref_1055_, lean_object* v_msg_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2(v_00_u03b1_1054_, v_ref_1055_, v_msg_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v_ref_1055_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5(lean_object* v_n_1063_, lean_object* v_as_1064_, lean_object* v_lo_1065_, lean_object* v_hi_1066_, lean_object* v_w_1067_, lean_object* v_hlo_1068_, lean_object* v_hhi_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(v_n_1063_, v_as_1064_, v_lo_1065_, v_hi_1066_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___boxed(lean_object* v_n_1071_, lean_object* v_as_1072_, lean_object* v_lo_1073_, lean_object* v_hi_1074_, lean_object* v_w_1075_, lean_object* v_hlo_1076_, lean_object* v_hhi_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5(v_n_1071_, v_as_1072_, v_lo_1073_, v_hi_1074_, v_w_1075_, v_hlo_1076_, v_hhi_1077_);
lean_dec(v_hi_1074_);
lean_dec(v_n_1071_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3(lean_object* v_00_u03b1_1079_, lean_object* v_msg_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg(v_msg_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1087_, lean_object* v_msg_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3(v_00_u03b1_1087_, v_msg_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8(lean_object* v_n_1095_, lean_object* v_lo_1096_, lean_object* v_hi_1097_, lean_object* v_hhi_1098_, lean_object* v_pivot_1099_, lean_object* v_as_1100_, lean_object* v_i_1101_, lean_object* v_k_1102_, lean_object* v_ilo_1103_, lean_object* v_ik_1104_, lean_object* v_w_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___redArg(v_hi_1097_, v_pivot_1099_, v_as_1100_, v_i_1101_, v_k_1102_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___boxed(lean_object* v_n_1107_, lean_object* v_lo_1108_, lean_object* v_hi_1109_, lean_object* v_hhi_1110_, lean_object* v_pivot_1111_, lean_object* v_as_1112_, lean_object* v_i_1113_, lean_object* v_k_1114_, lean_object* v_ilo_1115_, lean_object* v_ik_1116_, lean_object* v_w_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8(v_n_1107_, v_lo_1108_, v_hi_1109_, v_hhi_1110_, v_pivot_1111_, v_as_1112_, v_i_1113_, v_k_1114_, v_ilo_1115_, v_ik_1116_, v_w_1117_);
lean_dec(v_pivot_1111_);
lean_dec(v_hi_1109_);
lean_dec(v_lo_1108_);
lean_dec(v_n_1107_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10(lean_object* v_00_u03b1_1119_, lean_object* v_constName_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg(v_constName_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___boxed(lean_object* v_00_u03b1_1127_, lean_object* v_constName_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10(v_00_u03b1_1127_, v_constName_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14(lean_object* v_00_u03b1_1135_, lean_object* v_ref_1136_, lean_object* v_constName_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg(v_ref_1136_, v_constName_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___boxed(lean_object* v_00_u03b1_1144_, lean_object* v_ref_1145_, lean_object* v_constName_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14(v_00_u03b1_1144_, v_ref_1145_, v_constName_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v_ref_1145_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15(lean_object* v_00_u03b1_1153_, lean_object* v_ref_1154_, lean_object* v_msg_1155_, lean_object* v_declHint_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg(v_ref_1154_, v_msg_1155_, v_declHint_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___boxed(lean_object* v_00_u03b1_1163_, lean_object* v_ref_1164_, lean_object* v_msg_1165_, lean_object* v_declHint_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15(v_00_u03b1_1163_, v_ref_1164_, v_msg_1165_, v_declHint_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v_ref_1164_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17(lean_object* v_msg_1173_, lean_object* v_declHint_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg(v_msg_1173_, v_declHint_1174_, v___y_1178_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___boxed(lean_object* v_msg_1181_, lean_object* v_declHint_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17(v_msg_1181_, v_declHint_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(lean_object* v_x_1189_, lean_object* v_x_1190_, lean_object* v_x_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_box(0);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object* v_x_1196_, lean_object* v_x_1197_, lean_object* v_x_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(v_x_1196_, v_x_1197_, v_x_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v_x_1198_);
lean_dec_ref(v_x_1197_);
lean_dec(v_x_1196_);
return v_res_1201_;
}
}
static uint64_t _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1208_; uint64_t v___x_1209_; 
v___x_1208_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_));
v___x_1209_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1208_);
return v___x_1209_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1210_ = lean_uint64_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1211_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_));
v___x_1212_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
lean_ctor_set_uint64(v___x_1212_, sizeof(void*)*1, v___x_1210_);
return v___x_1212_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0);
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
return v___x_1214_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1215_ = lean_box(1);
v___x_1216_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4);
v___x_1217_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1218_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
lean_ctor_set(v___x_1218_, 1, v___x_1216_);
lean_ctor_set(v___x_1218_, 2, v___x_1215_);
return v___x_1218_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1222_ = lean_unsigned_to_nat(0u);
v___x_1223_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
lean_ctor_set(v___x_1223_, 2, v___x_1222_);
lean_ctor_set(v___x_1223_, 3, v___x_1222_);
lean_ctor_set(v___x_1223_, 4, v___x_1221_);
lean_ctor_set(v___x_1223_, 5, v___x_1221_);
lean_ctor_set(v___x_1223_, 6, v___x_1221_);
lean_ctor_set(v___x_1223_, 7, v___x_1221_);
lean_ctor_set(v___x_1223_, 8, v___x_1221_);
lean_ctor_set(v___x_1223_, 9, v___x_1221_);
lean_ctor_set(v___x_1223_, 10, v___x_1221_);
return v___x_1223_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1225_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
lean_ctor_set(v___x_1225_, 2, v___x_1224_);
lean_ctor_set(v___x_1225_, 3, v___x_1224_);
lean_ctor_set(v___x_1225_, 4, v___x_1224_);
lean_ctor_set(v___x_1225_, 5, v___x_1224_);
return v___x_1225_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
lean_ctor_set(v___x_1227_, 2, v___x_1226_);
lean_ctor_set(v___x_1227_, 3, v___x_1226_);
lean_ctor_set(v___x_1227_, 4, v___x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(lean_object* v___x_1228_, lean_object* v_declName_1229_, lean_object* v_stx_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v_args_1236_; uint8_t v___x_1237_; uint8_t v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1234_ = lean_unsigned_to_nat(1u);
v___x_1235_ = l_Lean_Syntax_getArg(v_stx_1230_, v___x_1234_);
v_args_1236_ = l_Lean_Syntax_getArgs(v___x_1235_);
lean_dec(v___x_1235_);
v___x_1237_ = 0;
v___x_1238_ = 1;
v___x_1239_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1240_ = lean_unsigned_to_nat(0u);
v___x_1241_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4);
v___x_1242_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1243_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_));
v___x_1244_ = lean_box(0);
lean_inc(v___x_1228_);
v___x_1245_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1245_, 0, v___x_1239_);
lean_ctor_set(v___x_1245_, 1, v___x_1228_);
lean_ctor_set(v___x_1245_, 2, v___x_1242_);
lean_ctor_set(v___x_1245_, 3, v___x_1243_);
lean_ctor_set(v___x_1245_, 4, v___x_1244_);
lean_ctor_set(v___x_1245_, 5, v___x_1240_);
lean_ctor_set(v___x_1245_, 6, v___x_1244_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*7, v___x_1237_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*7 + 1, v___x_1237_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*7 + 2, v___x_1237_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*7 + 3, v___x_1238_);
v___x_1246_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1247_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1248_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1246_);
lean_ctor_set(v___x_1249_, 1, v___x_1247_);
lean_ctor_set(v___x_1249_, 2, v___x_1228_);
lean_ctor_set(v___x_1249_, 3, v___x_1241_);
lean_ctor_set(v___x_1249_, 4, v___x_1248_);
v___x_1250_ = lean_st_mk_ref(v___x_1249_);
v___x_1251_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs(v_declName_1229_, v_args_1236_, v___x_1245_, v___x_1250_, v___y_1231_, v___y_1232_);
lean_dec_ref_known(v___x_1245_, 7);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1260_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1254_ = v___x_1251_;
v_isShared_1255_ = v_isSharedCheck_1260_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1251_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1260_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; lean_object* v___x_1258_; 
v___x_1256_ = lean_st_ref_get(v___x_1250_);
lean_dec(v___x_1250_);
lean_dec(v___x_1256_);
if (v_isShared_1255_ == 0)
{
v___x_1258_ = v___x_1254_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1252_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
else
{
lean_dec(v___x_1250_);
return v___x_1251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object* v___x_1261_, lean_object* v_declName_1262_, lean_object* v_stx_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(v___x_1261_, v_declName_1262_, v_stx_1263_, v___y_1264_, v___y_1265_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v_stx_1263_);
return v_res_1267_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(uint8_t v___x_1268_, lean_object* v_env_1269_, lean_object* v_n_1270_, lean_object* v_x_1271_){
_start:
{
uint8_t v___x_1272_; 
v___x_1272_ = l_Lean_Environment_contains(v_env_1269_, v_n_1270_, v___x_1268_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object* v___x_1273_, lean_object* v_env_1274_, lean_object* v_n_1275_, lean_object* v_x_1276_){
_start:
{
uint8_t v___x_576__boxed_1277_; uint8_t v_res_1278_; lean_object* v_r_1279_; 
v___x_576__boxed_1277_ = lean_unbox(v___x_1273_);
v_res_1278_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(v___x_576__boxed_1277_, v_env_1274_, v_n_1275_, v_x_1276_);
lean_dec_ref(v_x_1276_);
v_r_1279_ = lean_box(v_res_1278_);
return v_r_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_));
v___x_1308_ = l_Lean_registerParametricAttribute___redArg(v___x_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object* v_a_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_();
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1(){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_));
v___x_1314_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1___closed__0));
v___x_1315_ = l_Lean_addBuiltinDocString(v___x_1313_, v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1___boxed(lean_object* v_a_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1();
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3(){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1344_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_));
v___x_1345_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__6));
v___x_1346_ = l_Lean_addBuiltinDeclarationRanges(v___x_1344_, v___x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___boxed(lean_object* v_a_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3();
return v_res_1348_;
}
}
static lean_object* _init_l_Lean_Compiler_getSpecializationArgs_x3f___closed__0(void){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Array_instInhabited___redArg();
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getSpecializationArgs_x3f(lean_object* v_env_1350_, lean_object* v_declName_1351_){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1352_ = lean_obj_once(&l_Lean_Compiler_getSpecializationArgs_x3f___closed__0, &l_Lean_Compiler_getSpecializationArgs_x3f___closed__0_once, _init_l_Lean_Compiler_getSpecializationArgs_x3f___closed__0);
v___x_1353_ = l_Lean_Compiler_specializeAttr;
v___x_1354_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_1352_, v___x_1353_, v_env_1350_, v_declName_1351_);
return v___x_1354_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_hasSpecializeAttribute(lean_object* v_env_1355_, lean_object* v_declName_1356_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_Compiler_getSpecializationArgs_x3f(v_env_1355_, v_declName_1356_);
if (lean_obj_tag(v___x_1357_) == 0)
{
uint8_t v___x_1358_; 
v___x_1358_ = 0;
return v___x_1358_;
}
else
{
uint8_t v___x_1359_; 
lean_dec_ref_known(v___x_1357_, 1);
v___x_1359_ = 1;
return v___x_1359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasSpecializeAttribute___boxed(lean_object* v_env_1360_, lean_object* v_declName_1361_){
_start:
{
uint8_t v_res_1362_; lean_object* v_r_1363_; 
v_res_1362_ = l_Lean_Compiler_hasSpecializeAttribute(v_env_1360_, v_declName_1361_);
v_r_1363_ = lean_box(v_res_1362_);
return v_r_1363_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_hasNospecializeAttribute(lean_object* v_env_1364_, lean_object* v_declName_1365_){
_start:
{
lean_object* v___x_1366_; uint8_t v___x_1367_; 
v___x_1366_ = l_Lean_Compiler_nospecializeAttr;
v___x_1367_ = l_Lean_TagAttribute_hasTag(v___x_1366_, v_env_1364_, v_declName_1365_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasNospecializeAttribute___boxed(lean_object* v_env_1368_, lean_object* v_declName_1369_){
_start:
{
uint8_t v_res_1370_; lean_object* v_r_1371_; 
v_res_1370_ = l_Lean_Compiler_hasNospecializeAttribute(v_env_1368_, v_declName_1369_);
v_r_1371_ = lean_box(v_res_1370_);
return v_r_1371_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_hasWeakSpecializeAttribute(lean_object* v_env_1372_, lean_object* v_declName_1373_){
_start:
{
lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1374_ = l_Lean_Compiler_weakSpecializeAttr;
v___x_1375_ = l_Lean_TagAttribute_hasTag(v___x_1374_, v_env_1372_, v_declName_1373_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasWeakSpecializeAttribute___boxed(lean_object* v_env_1376_, lean_object* v_declName_1377_){
_start:
{
uint8_t v_res_1378_; lean_object* v_r_1379_; 
v_res_1378_ = l_Lean_Compiler_hasWeakSpecializeAttribute(v_env_1376_, v_declName_1377_);
v_r_1379_ = lean_box(v_res_1378_);
return v_r_1379_;
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
