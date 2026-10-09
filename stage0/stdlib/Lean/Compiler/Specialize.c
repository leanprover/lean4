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
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__27;
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
LEAN_EXPORT uint8_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "specializeAttr"};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 4, 174, 8, 190, 202, 8, 76)}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "specialize"};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(241, 143, 174, 76, 41, 16, 248, 244)}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "mark definition to always be specialized"};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_Compiler_SpecializeAttributeKind_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lean_Compiler_SpecializeAttributeKind_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Compiler_SpecializeAttributeKind_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Compiler_SpecializeAttributeKind_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lean_Compiler_SpecializeAttributeKind_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_Compiler_SpecializeAttributeKind_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_Compiler_SpecializeAttributeKind_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_specialize_elim___redArg(lean_object* v_specialize_24_){
_start:
{
lean_inc(v_specialize_24_);
return v_specialize_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_specialize_elim___redArg___boxed(lean_object* v_specialize_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Compiler_SpecializeAttributeKind_specialize_elim___redArg(v_specialize_25_);
lean_dec(v_specialize_25_);
return v_res_26_;
}
}
lean_object* l_Lean_Compiler_SpecializeAttributeKind_specialize_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_specialize_30_){
_start:
{
lean_inc(v_specialize_30_);
return v_specialize_30_;
}
}
LEAN_EXPORT void l_Lean_Compiler_SpecializeAttributeKind_specialize_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_specialize_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Compiler_SpecializeAttributeKind_specialize_elim(lean_box(0), v_t_28_, lean_box(0), v_specialize_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_specialize_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_specialize_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_Compiler_SpecializeAttributeKind_specialize_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_specialize_35_);
lean_dec(v_specialize_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim___redArg(lean_object* v_nospecialize_38_){
_start:
{
lean_inc(v_nospecialize_38_);
return v_nospecialize_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim___redArg___boxed(lean_object* v_nospecialize_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim___redArg(v_nospecialize_39_);
lean_dec(v_nospecialize_39_);
return v_res_40_;
}
}
lean_object* l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_nospecialize_44_){
_start:
{
lean_inc(v_nospecialize_44_);
return v_nospecialize_44_;
}
}
LEAN_EXPORT void l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_nospecialize_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim(lean_box(0), v_t_42_, lean_box(0), v_nospecialize_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_nospecialize_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_nospecialize_49_);
lean_dec(v_nospecialize_49_);
return v_res_51_;
}
}
static uint8_t _init_l_Lean_Compiler_instInhabitedSpecializeAttributeKind_default(void){
_start:
{
uint8_t v___x_52_; 
v___x_52_ = 0;
return v___x_52_;
}
}
static uint8_t _init_l_Lean_Compiler_instInhabitedSpecializeAttributeKind(void){
_start:
{
uint8_t v___x_53_; 
v___x_53_ = 0;
return v___x_53_;
}
}
uint8_t l_Lean_Compiler_instBEqSpecializeAttributeKind_beq(uint8_t v_x_54_, uint8_t v_y_55_){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_56_ = lean_box(v_x_54_);
v___x_57_ = lean_obj_tag_nat(v___x_56_);
lean_dec(v___x_56_);
v___x_58_ = lean_box(v_y_55_);
v___x_59_ = lean_obj_tag_nat(v___x_58_);
lean_dec(v___x_58_);
v___x_60_ = lean_nat_dec_eq(v___x_57_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT void l_Lean_Compiler_instBEqSpecializeAttributeKind_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_54_ = stack[0].m_num;
uint8_t v_y_55_ = stack[1].m_num;
uint8_t v_res_61_;
v_res_61_ = l_Lean_Compiler_instBEqSpecializeAttributeKind_beq(v_x_54_, v_y_55_);
stack->m_num = v_res_61_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_instBEqSpecializeAttributeKind_beq___boxed(lean_object* v_x_62_, lean_object* v_y_63_){
_start:
{
uint8_t v_x_24__boxed_64_; uint8_t v_y_25__boxed_65_; uint8_t v_res_66_; lean_object* v_r_67_; 
v_x_24__boxed_64_ = lean_unbox(v_x_62_);
v_y_25__boxed_65_ = lean_unbox(v_y_63_);
v_res_66_ = l_Lean_Compiler_instBEqSpecializeAttributeKind_beq(v_x_24__boxed_64_, v_y_25__boxed_65_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_(lean_object* v_x_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_box(0);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_x_70_ = stack[0].m_obj;
lean_object* v___y_71_ = stack[1].m_obj;
lean_object* v___y_72_ = stack[2].m_obj;
lean_object* v_res_76_;
v_res_76_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_(v_x_70_, v___y_71_, v___y_72_);
stack->m_obj
 = v_res_76_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2____boxed(lean_object* v_x_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_(v_x_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v_x_77_);
return v_res_81_;
}
}
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; 
v___f_95_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_96_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_97_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_98_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_99_ = 0;
v___x_100_ = lean_box(2);
v___x_101_ = 0;
v___x_102_ = l_Lean_registerTagAttribute(v___x_96_, v___x_97_, v___f_95_, v___x_98_, v___x_99_, v___x_100_, v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_103_;
v_res_103_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_();
stack->m_obj
 = v_res_103_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2____boxed(lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_();
return v_res_105_;
}
}
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1(){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_109_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1___closed__0));
v___x_110_ = l_Lean_addBuiltinDocString(v___x_108_, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_111_;
v_res_111_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1();
stack->m_obj
 = v_res_111_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1___boxed(lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1();
return v_res_113_;
}
}
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3(){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_141_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__6));
v___x_142_ = l_Lean_addBuiltinDeclarationRanges(v___x_140_, v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_143_;
v_res_143_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3();
stack->m_obj
 = v_res_143_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___boxed(lean_object* v_a_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3();
return v_res_145_;
}
}
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; lean_object* v___x_163_; 
v___f_156_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_));
v___x_157_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_));
v___x_158_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_));
v___x_159_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_));
v___x_160_ = 0;
v___x_161_ = lean_box(2);
v___x_162_ = 0;
v___x_163_ = l_Lean_registerTagAttribute(v___x_157_, v___x_158_, v___f_156_, v___x_159_, v___x_160_, v___x_161_, v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_164_;
v_res_164_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_();
stack->m_obj
 = v_res_164_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2____boxed(lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_();
return v_res_166_;
}
}
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1(){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_));
v___x_170_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1___closed__0));
v___x_171_ = l_Lean_addBuiltinDocString(v___x_169_, v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_172_;
v_res_172_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1();
stack->m_obj
 = v_res_172_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1___boxed(lean_object* v_a_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1();
return v_res_174_;
}
}
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3(){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_201_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_));
v___x_202_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__6));
v___x_203_ = l_Lean_addBuiltinDeclarationRanges(v___x_201_, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_204_;
v_res_204_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3();
stack->m_obj
 = v_res_204_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___boxed(lean_object* v_a_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3();
return v_res_206_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0(lean_object* v_k_207_, lean_object* v_b_208_, lean_object* v_c_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v___x_215_; 
lean_inc(v___y_213_);
lean_inc_ref(v___y_212_);
lean_inc(v___y_211_);
lean_inc_ref(v___y_210_);
v___x_215_ = lean_apply_7(v_k_207_, v_b_208_, v_c_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, lean_box(0));
return v___x_215_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_207_ = stack[0].m_obj;
lean_object* v_b_208_ = stack[1].m_obj;
lean_object* v_c_209_ = stack[2].m_obj;
lean_object* v___y_210_ = stack[3].m_obj;
lean_object* v___y_211_ = stack[4].m_obj;
lean_object* v___y_212_ = stack[5].m_obj;
lean_object* v___y_213_ = stack[6].m_obj;
lean_object* v_res_216_;
v_res_216_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0(v_k_207_, v_b_208_, v_c_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
stack->m_obj
 = v_res_216_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0___boxed(lean_object* v_k_217_, lean_object* v_b_218_, lean_object* v_c_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0(v_k_217_, v_b_218_, v_c_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
return v_res_225_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(lean_object* v_type_226_, lean_object* v_k_227_, uint8_t v_cleanupAnnotations_228_, uint8_t v_whnfType_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___f_235_; lean_object* v___x_236_; 
v___f_235_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_235_, 0, v_k_227_);
v___x_236_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_226_, v___f_235_, v_cleanupAnnotations_228_, v_whnfType_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_236_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_236_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
v_a_245_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_236_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_236_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_226_ = stack[0].m_obj;
lean_object* v_k_227_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_228_ = stack[2].m_num;
uint8_t v_whnfType_229_ = stack[3].m_num;
lean_object* v___y_230_ = stack[4].m_obj;
lean_object* v___y_231_ = stack[5].m_obj;
lean_object* v___y_232_ = stack[6].m_obj;
lean_object* v___y_233_ = stack[7].m_obj;
lean_object* v_res_253_;
v_res_253_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(v_type_226_, v_k_227_, v_cleanupAnnotations_228_, v_whnfType_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
stack->m_obj
 = v_res_253_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___boxed(lean_object* v_type_254_, lean_object* v_k_255_, lean_object* v_cleanupAnnotations_256_, lean_object* v_whnfType_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_263_; uint8_t v_whnfType_boxed_264_; lean_object* v_res_265_; 
v_cleanupAnnotations_boxed_263_ = lean_unbox(v_cleanupAnnotations_256_);
v_whnfType_boxed_264_ = lean_unbox(v_whnfType_257_);
v_res_265_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(v_type_254_, v_k_255_, v_cleanupAnnotations_boxed_263_, v_whnfType_boxed_264_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
return v_res_265_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7(lean_object* v_00_u03b1_266_, lean_object* v_type_267_, lean_object* v_k_268_, uint8_t v_cleanupAnnotations_269_, uint8_t v_whnfType_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(v_type_267_, v_k_268_, v_cleanupAnnotations_269_, v_whnfType_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
return v___x_276_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_267_ = stack[1].m_obj;
lean_object* v_k_268_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_269_ = stack[3].m_num;
uint8_t v_whnfType_270_ = stack[4].m_num;
lean_object* v___y_271_ = stack[5].m_obj;
lean_object* v___y_272_ = stack[6].m_obj;
lean_object* v___y_273_ = stack[7].m_obj;
lean_object* v___y_274_ = stack[8].m_obj;
lean_object* v_res_277_;
v_res_277_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7(lean_box(0), v_type_267_, v_k_268_, v_cleanupAnnotations_269_, v_whnfType_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
stack->m_obj
 = v_res_277_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___boxed(lean_object* v_00_u03b1_278_, lean_object* v_type_279_, lean_object* v_k_280_, lean_object* v_cleanupAnnotations_281_, lean_object* v_whnfType_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_288_; uint8_t v_whnfType_boxed_289_; lean_object* v_res_290_; 
v_cleanupAnnotations_boxed_288_ = lean_unbox(v_cleanupAnnotations_281_);
v_whnfType_boxed_289_ = lean_unbox(v_whnfType_282_);
v_res_290_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7(v_00_u03b1_278_, v_type_279_, v_k_280_, v_cleanupAnnotations_boxed_288_, v_whnfType_boxed_289_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___redArg(lean_object* v_hi_291_, lean_object* v_pivot_292_, lean_object* v_as_293_, lean_object* v_i_294_, lean_object* v_k_295_){
_start:
{
uint8_t v___x_296_; 
v___x_296_ = lean_nat_dec_lt(v_k_295_, v_hi_291_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec(v_k_295_);
v___x_297_ = lean_array_fswap(v_as_293_, v_i_294_, v_hi_291_);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v_i_294_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
return v___x_298_;
}
else
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = lean_array_fget_borrowed(v_as_293_, v_k_295_);
v___x_300_ = lean_nat_dec_lt(v___x_299_, v_pivot_292_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(1u);
v___x_302_ = lean_nat_add(v_k_295_, v___x_301_);
lean_dec(v_k_295_);
v_k_295_ = v___x_302_;
goto _start;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_304_ = lean_array_fswap(v_as_293_, v_i_294_, v_k_295_);
v___x_305_ = lean_unsigned_to_nat(1u);
v___x_306_ = lean_nat_add(v_i_294_, v___x_305_);
lean_dec(v_i_294_);
v___x_307_ = lean_nat_add(v_k_295_, v___x_305_);
lean_dec(v_k_295_);
v_as_293_ = v___x_304_;
v_i_294_ = v___x_306_;
v_k_295_ = v___x_307_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___redArg___boxed(lean_object* v_hi_309_, lean_object* v_pivot_310_, lean_object* v_as_311_, lean_object* v_i_312_, lean_object* v_k_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___redArg(v_hi_309_, v_pivot_310_, v_as_311_, v_i_312_, v_k_313_);
lean_dec(v_pivot_310_);
lean_dec(v_hi_309_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(lean_object* v_n_315_, lean_object* v_as_316_, lean_object* v_lo_317_, lean_object* v_hi_318_){
_start:
{
lean_object* v___y_320_; uint8_t v___x_330_; 
v___x_330_ = lean_nat_dec_lt(v_lo_317_, v_hi_318_);
if (v___x_330_ == 0)
{
lean_dec(v_lo_317_);
return v_as_316_;
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v_mid_333_; lean_object* v___y_335_; lean_object* v___y_341_; lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_331_ = lean_nat_add(v_lo_317_, v_hi_318_);
v___x_332_ = lean_unsigned_to_nat(1u);
v_mid_333_ = lean_nat_shiftr(v___x_331_, v___x_332_);
lean_dec(v___x_331_);
v___x_346_ = lean_array_fget_borrowed(v_as_316_, v_mid_333_);
v___x_347_ = lean_array_fget_borrowed(v_as_316_, v_lo_317_);
v___x_348_ = lean_nat_dec_lt(v___x_346_, v___x_347_);
if (v___x_348_ == 0)
{
v___y_341_ = v_as_316_;
goto v___jp_340_;
}
else
{
lean_object* v___x_349_; 
v___x_349_ = lean_array_fswap(v_as_316_, v_lo_317_, v_mid_333_);
v___y_341_ = v___x_349_;
goto v___jp_340_;
}
v___jp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_336_ = lean_array_fget_borrowed(v___y_335_, v_mid_333_);
v___x_337_ = lean_array_fget_borrowed(v___y_335_, v_hi_318_);
v___x_338_ = lean_nat_dec_lt(v___x_336_, v___x_337_);
if (v___x_338_ == 0)
{
lean_dec(v_mid_333_);
v___y_320_ = v___y_335_;
goto v___jp_319_;
}
else
{
lean_object* v___x_339_; 
v___x_339_ = lean_array_fswap(v___y_335_, v_mid_333_, v_hi_318_);
lean_dec(v_mid_333_);
v___y_320_ = v___x_339_;
goto v___jp_319_;
}
}
v___jp_340_:
{
lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_342_ = lean_array_fget_borrowed(v___y_341_, v_hi_318_);
v___x_343_ = lean_array_fget_borrowed(v___y_341_, v_lo_317_);
v___x_344_ = lean_nat_dec_lt(v___x_342_, v___x_343_);
if (v___x_344_ == 0)
{
v___y_335_ = v___y_341_;
goto v___jp_334_;
}
else
{
lean_object* v___x_345_; 
v___x_345_ = lean_array_fswap(v___y_341_, v_lo_317_, v_hi_318_);
v___y_335_ = v___x_345_;
goto v___jp_334_;
}
}
}
v___jp_319_:
{
lean_object* v_pivot_321_; lean_object* v___x_322_; lean_object* v_fst_323_; lean_object* v_snd_324_; uint8_t v___x_325_; 
v_pivot_321_ = lean_array_fget(v___y_320_, v_hi_318_);
lean_inc_n(v_lo_317_, 2);
v___x_322_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___redArg(v_hi_318_, v_pivot_321_, v___y_320_, v_lo_317_, v_lo_317_);
lean_dec(v_pivot_321_);
v_fst_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_fst_323_);
v_snd_324_ = lean_ctor_get(v___x_322_, 1);
lean_inc(v_snd_324_);
lean_dec_ref(v___x_322_);
v___x_325_ = lean_nat_dec_le(v_hi_318_, v_fst_323_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(v_n_315_, v_snd_324_, v_lo_317_, v_fst_323_);
v___x_327_ = lean_unsigned_to_nat(1u);
v___x_328_ = lean_nat_add(v_fst_323_, v___x_327_);
lean_dec(v_fst_323_);
v_as_316_ = v___x_326_;
v_lo_317_ = v___x_328_;
goto _start;
}
else
{
lean_dec(v_fst_323_);
lean_dec(v_lo_317_);
return v_snd_324_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg___boxed(lean_object* v_n_350_, lean_object* v_as_351_, lean_object* v_lo_352_, lean_object* v_hi_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(v_n_350_, v_as_351_, v_lo_352_, v_hi_353_);
lean_dec(v_hi_353_);
lean_dec(v_n_350_);
return v_res_354_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg(size_t v_sz_355_, size_t v_i_356_, lean_object* v_bs_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
uint8_t v___x_362_; 
v___x_362_ = lean_usize_dec_lt(v_i_356_, v_sz_355_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v_bs_357_);
return v___x_363_;
}
else
{
lean_object* v_v_364_; lean_object* v___x_365_; lean_object* v_bs_x27_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_v_364_ = lean_array_uget(v_bs_357_, v_i_356_);
v___x_365_ = lean_unsigned_to_nat(0u);
v_bs_x27_366_ = lean_array_uset(v_bs_357_, v_i_356_, v___x_365_);
v___x_367_ = l_Lean_Expr_fvarId_x21(v_v_364_);
lean_dec(v_v_364_);
v___x_368_ = l_Lean_FVarId_getUserName___redArg(v___x_367_, v___y_358_, v___y_359_, v___y_360_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; size_t v___x_370_; size_t v___x_371_; lean_object* v___x_372_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref_known(v___x_368_, 1);
v___x_370_ = ((size_t)1ULL);
v___x_371_ = lean_usize_add(v_i_356_, v___x_370_);
v___x_372_ = lean_array_uset(v_bs_x27_366_, v_i_356_, v_a_369_);
v_i_356_ = v___x_371_;
v_bs_357_ = v___x_372_;
goto _start;
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec_ref(v_bs_x27_366_);
v_a_374_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_368_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_368_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_355_ = stack[0].m_num;
size_t v_i_356_ = stack[1].m_num;
lean_object* v_bs_357_ = stack[2].m_obj;
lean_object* v___y_358_ = stack[3].m_obj;
lean_object* v___y_359_ = stack[4].m_obj;
lean_object* v___y_360_ = stack[5].m_obj;
lean_object* v_res_382_;
v_res_382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg(v_sz_355_, v_i_356_, v_bs_357_, v___y_358_, v___y_359_, v___y_360_);
stack->m_obj
 = v_res_382_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg___boxed(lean_object* v_sz_383_, lean_object* v_i_384_, lean_object* v_bs_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
size_t v_sz_boxed_390_; size_t v_i_boxed_391_; lean_object* v_res_392_; 
v_sz_boxed_390_ = lean_unbox_usize(v_sz_383_);
lean_dec(v_sz_383_);
v_i_boxed_391_ = lean_unbox_usize(v_i_384_);
lean_dec(v_i_384_);
v_res_392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg(v_sz_boxed_390_, v_i_boxed_391_, v_bs_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec_ref(v___y_386_);
return v_res_392_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1(lean_object* v_a_393_, lean_object* v_as_394_, size_t v_i_395_, size_t v_stop_396_){
_start:
{
uint8_t v___x_397_; 
v___x_397_ = lean_usize_dec_eq(v_i_395_, v_stop_396_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_398_ = lean_array_uget_borrowed(v_as_394_, v_i_395_);
v___x_399_ = lean_nat_dec_eq(v_a_393_, v___x_398_);
if (v___x_399_ == 0)
{
size_t v___x_400_; size_t v___x_401_; 
v___x_400_ = ((size_t)1ULL);
v___x_401_ = lean_usize_add(v_i_395_, v___x_400_);
v_i_395_ = v___x_401_;
goto _start;
}
else
{
return v___x_399_;
}
}
else
{
uint8_t v___x_403_; 
v___x_403_ = 0;
return v___x_403_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_393_ = stack[0].m_obj;
lean_object* v_as_394_ = stack[1].m_obj;
size_t v_i_395_ = stack[2].m_num;
size_t v_stop_396_ = stack[3].m_num;
uint8_t v_res_404_;
v_res_404_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1(v_a_393_, v_as_394_, v_i_395_, v_stop_396_);
stack->m_num = v_res_404_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1___boxed(lean_object* v_a_405_, lean_object* v_as_406_, lean_object* v_i_407_, lean_object* v_stop_408_){
_start:
{
size_t v_i_boxed_409_; size_t v_stop_boxed_410_; uint8_t v_res_411_; lean_object* v_r_412_; 
v_i_boxed_409_ = lean_unbox_usize(v_i_407_);
lean_dec(v_i_407_);
v_stop_boxed_410_ = lean_unbox_usize(v_stop_408_);
lean_dec(v_stop_408_);
v_res_411_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1(v_a_405_, v_as_406_, v_i_boxed_409_, v_stop_boxed_410_);
lean_dec_ref(v_as_406_);
lean_dec(v_a_405_);
v_r_412_ = lean_box(v_res_411_);
return v_r_412_;
}
}
uint8_t l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1(lean_object* v_as_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = lean_array_get_size(v_as_413_);
v___x_417_ = lean_nat_dec_lt(v___x_415_, v___x_416_);
if (v___x_417_ == 0)
{
return v___x_417_;
}
else
{
if (v___x_417_ == 0)
{
return v___x_417_;
}
else
{
size_t v___x_418_; size_t v___x_419_; uint8_t v___x_420_; 
v___x_418_ = ((size_t)0ULL);
v___x_419_ = lean_usize_of_nat(v___x_416_);
v___x_420_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1(v_a_414_, v_as_413_, v___x_418_, v___x_419_);
return v___x_420_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_413_ = stack[0].m_obj;
lean_object* v_a_414_ = stack[1].m_obj;
uint8_t v_res_421_;
v_res_421_ = l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1(v_as_413_, v_a_414_);
stack->m_num = v_res_421_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1___boxed(lean_object* v_as_422_, lean_object* v_a_423_){
_start:
{
uint8_t v_res_424_; lean_object* v_r_425_; 
v_res_424_ = l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1(v_as_422_, v_a_423_);
lean_dec(v_a_423_);
lean_dec_ref(v_as_422_);
v_r_425_ = lean_box(v_res_424_);
return v_r_425_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5_spec__8(lean_object* v_xs_426_, lean_object* v_v_427_, lean_object* v_i_428_){
_start:
{
lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_429_ = lean_array_get_size(v_xs_426_);
v___x_430_ = lean_nat_dec_lt(v_i_428_, v___x_429_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
lean_dec(v_i_428_);
v___x_431_ = lean_box(0);
return v___x_431_;
}
else
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = lean_array_fget_borrowed(v_xs_426_, v_i_428_);
v___x_433_ = lean_name_eq(v___x_432_, v_v_427_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_unsigned_to_nat(1u);
v___x_435_ = lean_nat_add(v_i_428_, v___x_434_);
lean_dec(v_i_428_);
v_i_428_ = v___x_435_;
goto _start;
}
else
{
lean_object* v___x_437_; 
v___x_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_437_, 0, v_i_428_);
return v___x_437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_438_, lean_object* v_v_439_, lean_object* v_i_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5_spec__8(v_xs_438_, v_v_439_, v_i_440_);
lean_dec(v_v_439_);
lean_dec_ref(v_xs_438_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5(lean_object* v_xs_442_, lean_object* v_v_443_){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5_spec__8(v_xs_442_, v_v_443_, v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5___boxed(lean_object* v_xs_446_, lean_object* v_v_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5(v_xs_446_, v_v_447_);
lean_dec(v_v_447_);
lean_dec_ref(v_xs_446_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3(lean_object* v_xs_449_, lean_object* v_v_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5(v_xs_449_, v_v_450_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v___x_452_; 
v___x_452_ = lean_box(0);
return v___x_452_;
}
else
{
lean_object* v_val_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
v_val_453_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v___x_451_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_val_453_);
lean_dec(v___x_451_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_val_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3___boxed(lean_object* v_xs_461_, lean_object* v_v_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3(v_xs_461_, v_v_462_);
lean_dec(v_v_462_);
lean_dec_ref(v_xs_461_);
return v_res_463_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5(lean_object* v_msgData_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v___x_470_; lean_object* v_env_471_; uint8_t v___x_472_; lean_object* v_env_473_; lean_object* v___x_474_; lean_object* v_toCold_475_; lean_object* v_mctx_476_; lean_object* v_lctx_477_; lean_object* v_options_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_470_ = lean_st_ref_get(v___y_468_);
v_env_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc_ref(v_env_471_);
lean_dec(v___x_470_);
v___x_472_ = 0;
v_env_473_ = l_Lean_Environment_setRecordingDeps(v_env_471_, v___x_472_);
v___x_474_ = lean_st_ref_get(v___y_466_);
v_toCold_475_ = lean_ctor_get(v___y_467_, 0);
v_mctx_476_ = lean_ctor_get(v___x_474_, 0);
lean_inc_ref(v_mctx_476_);
lean_dec(v___x_474_);
v_lctx_477_ = lean_ctor_get(v___y_465_, 2);
v_options_478_ = lean_ctor_get(v_toCold_475_, 2);
lean_inc_ref(v_options_478_);
lean_inc_ref(v_lctx_477_);
v___x_479_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_479_, 0, v_env_473_);
lean_ctor_set(v___x_479_, 1, v_mctx_476_);
lean_ctor_set(v___x_479_, 2, v_lctx_477_);
lean_ctor_set(v___x_479_, 3, v_options_478_);
v___x_480_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set(v___x_480_, 1, v_msgData_464_);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_464_ = stack[0].m_obj;
lean_object* v___y_465_ = stack[1].m_obj;
lean_object* v___y_466_ = stack[2].m_obj;
lean_object* v___y_467_ = stack[3].m_obj;
lean_object* v___y_468_ = stack[4].m_obj;
lean_object* v_res_482_;
v_res_482_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5(v_msgData_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
stack->m_obj
 = v_res_482_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5___boxed(lean_object* v_msgData_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5(v_msgData_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
return v_res_489_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg(lean_object* v_msg_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_ref_496_; lean_object* v___x_497_; lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_506_; 
v_ref_496_ = lean_ctor_get(v___y_493_, 2);
v___x_497_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5(v_msg_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
v_a_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_506_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_504_; 
lean_inc(v_ref_496_);
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v_ref_496_);
lean_ctor_set(v___x_502_, 1, v_a_498_);
if (v_isShared_501_ == 0)
{
lean_ctor_set_tag(v___x_500_, 1);
lean_ctor_set(v___x_500_, 0, v___x_502_);
v___x_504_ = v___x_500_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_490_ = stack[0].m_obj;
lean_object* v___y_491_ = stack[1].m_obj;
lean_object* v___y_492_ = stack[2].m_obj;
lean_object* v___y_493_ = stack[3].m_obj;
lean_object* v___y_494_ = stack[4].m_obj;
lean_object* v_res_507_;
v_res_507_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg(v_msg_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
stack->m_obj
 = v_res_507_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg___boxed(lean_object* v_msg_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg(v_msg_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
return v_res_514_;
}
}
lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(lean_object* v_ref_515_, lean_object* v_msg_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v_toCold_522_; lean_object* v_currRecDepth_523_; lean_object* v_ref_524_; uint16_t v_optionFlags_525_; uint8_t v_suppressElabErrors_526_; uint8_t v_isRecordingDeps_527_; lean_object* v_ref_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_toCold_522_ = lean_ctor_get(v___y_519_, 0);
v_currRecDepth_523_ = lean_ctor_get(v___y_519_, 1);
v_ref_524_ = lean_ctor_get(v___y_519_, 2);
v_optionFlags_525_ = lean_ctor_get_uint16(v___y_519_, sizeof(void*)*3);
v_suppressElabErrors_526_ = lean_ctor_get_uint8(v___y_519_, sizeof(void*)*3 + 2);
v_isRecordingDeps_527_ = lean_ctor_get_uint8(v___y_519_, sizeof(void*)*3 + 3);
v_ref_528_ = l_Lean_replaceRef(v_ref_515_, v_ref_524_);
lean_inc(v_currRecDepth_523_);
lean_inc_ref(v_toCold_522_);
v___x_529_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_529_, 0, v_toCold_522_);
lean_ctor_set(v___x_529_, 1, v_currRecDepth_523_);
lean_ctor_set(v___x_529_, 2, v_ref_528_);
lean_ctor_set_uint16(v___x_529_, sizeof(void*)*3, v_optionFlags_525_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*3 + 2, v_suppressElabErrors_526_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*3 + 3, v_isRecordingDeps_527_);
v___x_530_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg(v_msg_516_, v___y_517_, v___y_518_, v___x_529_, v___y_520_);
lean_dec_ref_known(v___x_529_, 3);
return v___x_530_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_515_ = stack[0].m_obj;
lean_object* v_msg_516_ = stack[1].m_obj;
lean_object* v___y_517_ = stack[2].m_obj;
lean_object* v___y_518_ = stack[3].m_obj;
lean_object* v___y_519_ = stack[4].m_obj;
lean_object* v___y_520_ = stack[5].m_obj;
lean_object* v_res_531_;
v_res_531_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_ref_515_, v_msg_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
stack->m_obj
 = v_res_531_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg___boxed(lean_object* v_ref_532_, lean_object* v_msg_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_ref_532_, v_msg_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v_ref_532_);
return v_res_539_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__0));
v___x_542_ = l_Lean_stringToMessageData(v___x_541_);
return v___x_542_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__2));
v___x_545_ = l_Lean_stringToMessageData(v___x_544_);
return v___x_545_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__4));
v___x_548_ = l_Lean_stringToMessageData(v___x_547_);
return v___x_548_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__6));
v___x_551_ = l_Lean_stringToMessageData(v___x_550_);
return v___x_551_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__8));
v___x_554_ = l_Lean_stringToMessageData(v___x_553_);
return v___x_554_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__10));
v___x_557_ = l_Lean_stringToMessageData(v___x_556_);
return v___x_557_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__12));
v___x_560_ = l_Lean_stringToMessageData(v___x_559_);
return v___x_560_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__14));
v___x_563_ = l_Lean_stringToMessageData(v___x_562_);
return v___x_563_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__16));
v___x_566_ = l_Lean_stringToMessageData(v___x_565_);
return v___x_566_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__18));
v___x_569_ = l_Lean_stringToMessageData(v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__20));
v___x_572_ = l_Lean_stringToMessageData(v___x_571_);
return v___x_572_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4(lean_object* v_a_573_, lean_object* v_declName_574_, lean_object* v___x_575_, lean_object* v_as_576_, size_t v_sz_577_, size_t v_i_578_, lean_object* v_b_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_a_586_; lean_object* v___y_591_; uint8_t v___x_593_; 
v___x_593_ = lean_usize_dec_lt(v_i_578_, v_sz_577_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; 
lean_dec(v_declName_574_);
v___x_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_594_, 0, v_b_579_);
return v___x_594_;
}
else
{
lean_object* v___x_595_; uint8_t v___x_596_; lean_object* v_a_597_; lean_object* v___x_598_; 
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = lean_nat_dec_eq(v___x_575_, v___x_595_);
v_a_597_ = lean_array_uget_borrowed(v_as_576_, v_i_578_);
v___x_598_ = l_Lean_Syntax_isNatLit_x3f(v_a_597_);
if (lean_obj_tag(v___x_598_) == 1)
{
lean_object* v_val_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_676_; 
v_val_599_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_676_ == 0)
{
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_676_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_val_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_676_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; uint8_t v___x_665_; 
v___x_665_ = lean_nat_dec_eq(v_val_599_, v___x_595_);
if (v___x_665_ == 0)
{
v___y_604_ = v___y_580_;
v___y_605_ = v___y_581_;
v___y_606_ = v___y_582_;
v___y_607_ = v___y_583_;
goto v___jp_603_;
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15);
v___x_667_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_597_, v___x_666_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_dec_ref_known(v___x_667_, 1);
v___y_604_ = v___y_580_;
v___y_605_ = v___y_581_;
v___y_606_ = v___y_582_;
v___y_607_ = v___y_583_;
goto v___jp_603_;
}
else
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
lean_del_object(v___x_601_);
lean_dec(v_val_599_);
lean_dec_ref(v_b_579_);
lean_dec(v_declName_574_);
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
v___jp_603_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_608_ = lean_unsigned_to_nat(1u);
v___x_609_ = lean_nat_sub(v_val_599_, v___x_608_);
lean_dec(v_val_599_);
v___x_610_ = lean_array_get_size(v_a_573_);
v___x_611_ = lean_nat_dec_le(v___x_610_, v___x_609_);
if (v___x_611_ == 0)
{
uint8_t v___x_612_; 
v___x_612_ = l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1(v_b_579_, v___x_609_);
if (v___x_612_ == 0)
{
lean_del_object(v___x_601_);
v___y_591_ = v___x_609_;
goto v___jp_590_;
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_613_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1);
v___x_614_ = lean_nat_add(v___x_609_, v___x_608_);
v___x_615_ = l_Nat_reprFast(v___x_614_);
if (v_isShared_602_ == 0)
{
lean_ctor_set_tag(v___x_601_, 3);
lean_ctor_set(v___x_601_, 0, v___x_615_);
v___x_617_ = v___x_601_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_615_);
v___x_617_ = v_reuseFailAlloc_636_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_618_ = l_Lean_MessageData_ofFormat(v___x_617_);
v___x_619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_613_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3);
v___x_621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_619_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = lean_array_fget_borrowed(v_a_573_, v___x_609_);
lean_inc(v___x_622_);
v___x_623_ = l_Lean_MessageData_ofName(v___x_622_);
v___x_624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_621_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5);
v___x_626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_597_, v___x_626_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_dec_ref_known(v___x_627_, 1);
v___y_591_ = v___x_609_;
goto v___jp_590_;
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec(v___x_609_);
lean_dec_ref(v_b_579_);
lean_dec(v_declName_574_);
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
else
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_637_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7);
v___x_638_ = l_Nat_reprFast(v___x_609_);
if (v_isShared_602_ == 0)
{
lean_ctor_set_tag(v___x_601_, 3);
lean_ctor_set(v___x_601_, 0, v___x_638_);
v___x_640_ = v___x_601_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_638_);
v___x_640_ = v_reuseFailAlloc_664_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_641_ = l_Lean_MessageData_ofFormat(v___x_640_);
v___x_642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_637_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9);
v___x_644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
lean_inc(v_declName_574_);
v___x_645_ = l_Lean_MessageData_ofConstName(v_declName_574_, v___x_596_);
v___x_646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
v___x_647_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11);
v___x_648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = l_Nat_reprFast(v___x_610_);
v___x_650_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
v___x_651_ = l_Lean_MessageData_ofFormat(v___x_650_);
v___x_652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_648_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13);
v___x_654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_597_, v___x_654_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_dec_ref_known(v___x_655_, 1);
v_a_586_ = v_b_579_;
goto v___jp_585_;
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
lean_dec_ref(v_b_579_);
lean_dec(v_declName_574_);
v_a_656_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_655_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_655_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
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
lean_object* v___x_677_; lean_object* v___x_678_; 
lean_dec(v___x_598_);
v___x_677_ = l_Lean_Syntax_getId(v_a_597_);
v___x_678_ = l_Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3(v_a_573_, v___x_677_);
if (lean_obj_tag(v___x_678_) == 1)
{
lean_object* v_val_679_; uint8_t v___x_682_; 
v_val_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_val_679_);
lean_dec_ref_known(v___x_678_, 1);
v___x_682_ = l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1(v_b_579_, v_val_679_);
if (v___x_682_ == 0)
{
lean_dec(v___x_677_);
goto v___jp_680_;
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_683_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17);
v___x_684_ = l_Lean_MessageData_ofName(v___x_677_);
v___x_685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_683_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19);
v___x_687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_685_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_597_, v___x_687_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_dec_ref_known(v___x_688_, 1);
goto v___jp_680_;
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec(v_val_679_);
lean_dec_ref(v_b_579_);
lean_dec(v_declName_574_);
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
v___jp_680_:
{
lean_object* v___x_681_; 
v___x_681_ = lean_array_push(v_b_579_, v_val_679_);
v_a_586_ = v___x_681_;
goto v___jp_585_;
}
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
lean_dec(v___x_678_);
v___x_697_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17);
v___x_698_ = l_Lean_MessageData_ofName(v___x_677_);
v___x_699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9);
v___x_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
lean_inc(v_declName_574_);
v___x_702_ = l_Lean_MessageData_ofConstName(v_declName_574_, v___x_596_);
v___x_703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21);
v___x_705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_597_, v___x_705_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_dec_ref_known(v___x_706_, 1);
v_a_586_ = v_b_579_;
goto v___jp_585_;
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec_ref(v_b_579_);
lean_dec(v_declName_574_);
v_a_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
}
v___jp_585_:
{
size_t v___x_587_; size_t v___x_588_; 
v___x_587_ = ((size_t)1ULL);
v___x_588_ = lean_usize_add(v_i_578_, v___x_587_);
v_i_578_ = v___x_588_;
v_b_579_ = v_a_586_;
goto _start;
}
v___jp_590_:
{
lean_object* v___x_592_; 
v___x_592_ = lean_array_push(v_b_579_, v___y_591_);
v_a_586_ = v___x_592_;
goto v___jp_585_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_573_ = stack[0].m_obj;
lean_object* v_declName_574_ = stack[1].m_obj;
lean_object* v___x_575_ = stack[2].m_obj;
lean_object* v_as_576_ = stack[3].m_obj;
size_t v_sz_577_ = stack[4].m_num;
size_t v_i_578_ = stack[5].m_num;
lean_object* v_b_579_ = stack[6].m_obj;
lean_object* v___y_580_ = stack[7].m_obj;
lean_object* v___y_581_ = stack[8].m_obj;
lean_object* v___y_582_ = stack[9].m_obj;
lean_object* v___y_583_ = stack[10].m_obj;
lean_object* v_res_715_;
v_res_715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4(v_a_573_, v_declName_574_, v___x_575_, v_as_576_, v_sz_577_, v_i_578_, v_b_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
stack->m_obj
 = v_res_715_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___boxed(lean_object* v_a_716_, lean_object* v_declName_717_, lean_object* v___x_718_, lean_object* v_as_719_, lean_object* v_sz_720_, lean_object* v_i_721_, lean_object* v_b_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
size_t v_sz_boxed_728_; size_t v_i_boxed_729_; lean_object* v_res_730_; 
v_sz_boxed_728_ = lean_unbox_usize(v_sz_720_);
lean_dec(v_sz_720_);
v_i_boxed_729_ = lean_unbox_usize(v_i_721_);
lean_dec(v_i_721_);
v_res_730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4(v_a_716_, v_declName_717_, v___x_718_, v_as_719_, v_sz_boxed_728_, v_i_boxed_729_, v_b_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec_ref(v_as_719_);
lean_dec(v___x_718_);
lean_dec_ref(v_a_716_);
return v_res_730_;
}
}
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0(lean_object* v___x_731_, lean_object* v_args_732_, lean_object* v_declName_733_, lean_object* v___x_734_, lean_object* v_xs_735_, lean_object* v_x_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
size_t v_sz_742_; size_t v___x_743_; lean_object* v___x_744_; 
v_sz_742_ = lean_array_size(v_xs_735_);
v___x_743_ = ((size_t)0ULL);
v___x_744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg(v_sz_742_, v___x_743_, v_xs_735_, v___y_737_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_768_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_768_ == 0)
{
v___x_747_ = v___x_744_;
v_isShared_748_ = v_isSharedCheck_768_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_768_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; size_t v_sz_750_; lean_object* v___x_751_; 
v___x_749_ = lean_mk_empty_array_with_capacity(v___x_731_);
v_sz_750_ = lean_array_size(v_args_732_);
v___x_751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4(v_a_745_, v_declName_733_, v___x_734_, v_args_732_, v_sz_750_, v___x_743_, v___x_749_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec(v_a_745_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_753_; lean_object* v___y_755_; lean_object* v___y_756_; uint8_t v___x_761_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v___x_753_ = lean_array_get_size(v_a_752_);
v___x_761_ = lean_nat_dec_eq(v___x_753_, v___x_731_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___y_765_; uint8_t v___x_767_; 
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_751_, 1);
v___x_762_ = lean_unsigned_to_nat(1u);
v___x_763_ = lean_nat_sub(v___x_753_, v___x_762_);
v___x_767_ = lean_nat_dec_le(v___x_731_, v___x_763_);
if (v___x_767_ == 0)
{
lean_dec(v___x_731_);
lean_inc(v___x_763_);
v___y_765_ = v___x_763_;
goto v___jp_764_;
}
else
{
v___y_765_ = v___x_731_;
goto v___jp_764_;
}
v___jp_764_:
{
uint8_t v___x_766_; 
v___x_766_ = lean_nat_dec_le(v___y_765_, v___x_763_);
if (v___x_766_ == 0)
{
lean_dec(v___x_763_);
lean_inc(v___y_765_);
v___y_755_ = v___y_765_;
v___y_756_ = v___y_765_;
goto v___jp_754_;
}
else
{
v___y_755_ = v___y_765_;
v___y_756_ = v___x_763_;
goto v___jp_754_;
}
}
}
else
{
lean_del_object(v___x_747_);
lean_dec(v___x_731_);
return v___x_751_;
}
v___jp_754_:
{
lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_757_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(v___x_753_, v_a_752_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_757_);
v___x_759_ = v___x_747_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
else
{
lean_del_object(v___x_747_);
lean_dec(v___x_731_);
return v___x_751_;
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec(v_declName_733_);
lean_dec(v___x_731_);
v_a_769_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_744_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_744_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_731_ = stack[0].m_obj;
lean_object* v_args_732_ = stack[1].m_obj;
lean_object* v_declName_733_ = stack[2].m_obj;
lean_object* v___x_734_ = stack[3].m_obj;
lean_object* v_xs_735_ = stack[4].m_obj;
lean_object* v_x_736_ = stack[5].m_obj;
lean_object* v___y_737_ = stack[6].m_obj;
lean_object* v___y_738_ = stack[7].m_obj;
lean_object* v___y_739_ = stack[8].m_obj;
lean_object* v___y_740_ = stack[9].m_obj;
lean_object* v_res_777_;
v_res_777_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0(v___x_731_, v_args_732_, v_declName_733_, v___x_734_, v_xs_735_, v_x_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
stack->m_obj
 = v_res_777_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0___boxed(lean_object* v___x_778_, lean_object* v_args_779_, lean_object* v_declName_780_, lean_object* v___x_781_, lean_object* v_xs_782_, lean_object* v_x_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0(v___x_778_, v_args_779_, v_declName_780_, v___x_781_, v_xs_782_, v_x_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec_ref(v_x_783_);
lean_dec(v___x_781_);
lean_dec_ref(v_args_779_);
return v_res_789_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0(void){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_790_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__2(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_793_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_794_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1);
v___x_795_ = lean_unsigned_to_nat(0u);
v___x_796_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
lean_ctor_set(v___x_796_, 2, v___x_795_);
lean_ctor_set(v___x_796_, 3, v___x_795_);
lean_ctor_set(v___x_796_, 4, v___x_794_);
lean_ctor_set(v___x_796_, 5, v___x_794_);
lean_ctor_set(v___x_796_, 6, v___x_794_);
lean_ctor_set(v___x_796_, 7, v___x_794_);
lean_ctor_set(v___x_796_, 8, v___x_794_);
lean_ctor_set(v___x_796_, 9, v___x_794_);
lean_ctor_set(v___x_796_, 10, v___x_794_);
lean_ctor_set(v___x_796_, 11, v___x_793_);
return v___x_796_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_797_ = lean_unsigned_to_nat(32u);
v___x_798_ = lean_mk_empty_array_with_capacity(v___x_797_);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4(void){
_start:
{
size_t v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_800_ = ((size_t)5ULL);
v___x_801_ = lean_unsigned_to_nat(0u);
v___x_802_ = lean_unsigned_to_nat(32u);
v___x_803_ = lean_mk_empty_array_with_capacity(v___x_802_);
v___x_804_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__3);
v___x_805_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v___x_803_);
lean_ctor_set(v___x_805_, 2, v___x_801_);
lean_ctor_set(v___x_805_, 3, v___x_801_);
lean_ctor_set_usize(v___x_805_, 4, v___x_800_);
return v___x_805_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__5(void){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_806_ = lean_box(1);
v___x_807_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4);
v___x_808_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1);
v___x_809_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
lean_ctor_set(v___x_809_, 1, v___x_807_);
lean_ctor_set(v___x_809_, 2, v___x_806_);
return v___x_809_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__6));
v___x_812_ = l_Lean_stringToMessageData(v___x_811_);
return v___x_812_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__9(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__8));
v___x_815_ = l_Lean_stringToMessageData(v___x_814_);
return v___x_815_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__11(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__10));
v___x_818_ = l_Lean_stringToMessageData(v___x_817_);
return v___x_818_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__13(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__12));
v___x_821_ = l_Lean_stringToMessageData(v___x_820_);
return v___x_821_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__15(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__14));
v___x_824_ = l_Lean_stringToMessageData(v___x_823_);
return v___x_824_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__17(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__16));
v___x_827_ = l_Lean_stringToMessageData(v___x_826_);
return v___x_827_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__19(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__18));
v___x_830_ = l_Lean_stringToMessageData(v___x_829_);
return v___x_830_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__21(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__20));
v___x_833_ = l_Lean_stringToMessageData(v___x_832_);
return v___x_833_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__23(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__22));
v___x_836_ = l_Lean_stringToMessageData(v___x_835_);
return v___x_836_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__25(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__24));
v___x_839_ = l_Lean_stringToMessageData(v___x_838_);
return v___x_839_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__27(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__26));
v___x_842_ = l_Lean_stringToMessageData(v___x_841_);
return v___x_842_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg(lean_object* v_msg_843_, lean_object* v_declHint_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v_env_849_; uint8_t v___x_850_; 
v___x_847_ = lean_box(0);
v___x_848_ = lean_st_ref_get(v___y_845_);
v_env_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc_ref(v_env_849_);
lean_dec(v___x_848_);
v___x_850_ = l_Lean_Name_isAnonymous(v_declHint_844_);
if (v___x_850_ == 0)
{
uint8_t v_isExporting_851_; 
v_isExporting_851_ = lean_ctor_get_uint8(v_env_849_, sizeof(void*)*13);
if (v_isExporting_851_ == 0)
{
lean_object* v___x_852_; 
lean_dec_ref(v_env_849_);
lean_dec(v_declHint_844_);
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v_msg_843_);
return v___x_852_;
}
else
{
lean_object* v___x_853_; uint8_t v___x_854_; 
lean_inc_ref(v_env_849_);
v___x_853_ = l_Lean_Environment_setExporting(v_env_849_, v___x_850_);
lean_inc(v_declHint_844_);
lean_inc_ref(v___x_853_);
v___x_854_ = l_Lean_Environment_contains(v___x_853_, v_declHint_844_, v_isExporting_851_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; 
lean_dec_ref(v___x_853_);
lean_dec_ref(v_env_849_);
lean_dec(v_declHint_844_);
v___x_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_855_, 0, v_msg_843_);
return v___x_855_;
}
else
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v_c_861_; lean_object* v___x_862_; 
v___x_856_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__2);
v___x_857_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__5);
v___x_858_ = l_Lean_Options_empty;
v___x_859_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_859_, 0, v___x_853_);
lean_ctor_set(v___x_859_, 1, v___x_856_);
lean_ctor_set(v___x_859_, 2, v___x_857_);
lean_ctor_set(v___x_859_, 3, v___x_858_);
lean_inc(v_declHint_844_);
v___x_860_ = l_Lean_MessageData_ofConstName(v_declHint_844_, v___x_850_);
v_c_861_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_861_, 0, v___x_859_);
lean_ctor_set(v_c_861_, 1, v___x_860_);
v___x_862_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_849_, v_declHint_844_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
lean_dec_ref(v_env_849_);
lean_dec(v_declHint_844_);
v___x_863_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7);
v___x_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v_c_861_);
v___x_865_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__9);
v___x_866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_864_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = l_Lean_MessageData_note(v___x_866_);
v___x_868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_868_, 0, v_msg_843_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
return v___x_869_;
}
else
{
lean_object* v_val_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_926_; 
v_val_870_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_926_ == 0)
{
v___x_872_ = v___x_862_;
v_isShared_873_ = v_isSharedCheck_926_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_val_870_);
lean_dec(v___x_862_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_926_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v_modules_875_; lean_object* v_moduleNames_876_; lean_object* v_mod_877_; uint8_t v___y_879_; uint8_t v___x_909_; 
v___x_874_ = l_Lean_Environment_header(v_env_849_);
lean_dec_ref(v_env_849_);
v_modules_875_ = lean_ctor_get(v___x_874_, 3);
lean_inc_ref(v_modules_875_);
v_moduleNames_876_ = lean_ctor_get(v___x_874_, 4);
lean_inc_ref(v_moduleNames_876_);
lean_dec_ref(v___x_874_);
v_mod_877_ = lean_array_get(v___x_847_, v_moduleNames_876_, v_val_870_);
lean_dec_ref(v_moduleNames_876_);
v___x_909_ = l_Lean_isPrivateName(v_declHint_844_);
lean_dec(v_declHint_844_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_910_ = lean_array_get_size(v_modules_875_);
v___x_911_ = lean_nat_dec_lt(v_val_870_, v___x_910_);
if (v___x_911_ == 0)
{
lean_dec_ref(v_modules_875_);
lean_dec(v_val_870_);
v___y_879_ = v___x_909_;
goto v___jp_878_;
}
else
{
lean_object* v___x_912_; lean_object* v_toImport_913_; uint8_t v_isExported_914_; 
v___x_912_ = lean_array_fget(v_modules_875_, v_val_870_);
lean_dec(v_val_870_);
lean_dec_ref(v_modules_875_);
v_toImport_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc_ref(v_toImport_913_);
lean_dec(v___x_912_);
v_isExported_914_ = lean_ctor_get_uint8(v_toImport_913_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_913_);
v___y_879_ = v_isExported_914_;
goto v___jp_878_;
}
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
lean_dec_ref(v_modules_875_);
lean_del_object(v___x_872_);
lean_dec(v_val_870_);
v___x_915_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7);
v___x_916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set(v___x_916_, 1, v_c_861_);
v___x_917_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__25);
v___x_918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = l_Lean_MessageData_ofName(v_mod_877_);
v___x_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__27);
v___x_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_920_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = l_Lean_MessageData_note(v___x_922_);
v___x_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_924_, 0, v_msg_843_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
return v___x_925_;
}
v___jp_878_:
{
if (v___y_879_ == 0)
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_891_; 
v___x_880_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__11);
v___x_881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
lean_ctor_set(v___x_881_, 1, v_c_861_);
v___x_882_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__13);
v___x_883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_881_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = l_Lean_MessageData_ofName(v_mod_877_);
v___x_885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_883_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__15);
v___x_887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = l_Lean_MessageData_note(v___x_887_);
v___x_889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_889_, 0, v_msg_843_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
if (v_isShared_873_ == 0)
{
lean_ctor_set_tag(v___x_872_, 0);
lean_ctor_set(v___x_872_, 0, v___x_889_);
v___x_891_ = v___x_872_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_893_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__17);
v___x_894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
lean_ctor_set(v___x_894_, 1, v_c_861_);
v___x_895_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__19);
v___x_896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = l_Lean_MessageData_ofName(v_mod_877_);
lean_inc_ref(v___x_897_);
v___x_898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__21);
v___x_900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v___x_897_);
v___x_902_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__23);
v___x_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = l_Lean_MessageData_note(v___x_903_);
v___x_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_905_, 0, v_msg_843_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
if (v_isShared_873_ == 0)
{
lean_ctor_set_tag(v___x_872_, 0);
lean_ctor_set(v___x_872_, 0, v___x_905_);
v___x_907_ = v___x_872_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
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
lean_object* v___x_927_; 
lean_dec_ref(v_env_849_);
lean_dec(v_declHint_844_);
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v_msg_843_);
return v___x_927_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_843_ = stack[0].m_obj;
lean_object* v_declHint_844_ = stack[1].m_obj;
lean_object* v___y_845_ = stack[2].m_obj;
lean_object* v_res_928_;
v_res_928_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg(v_msg_843_, v_declHint_844_, v___y_845_);
stack->m_obj
 = v_res_928_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___boxed(lean_object* v_msg_929_, lean_object* v_declHint_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg(v_msg_929_, v_declHint_930_, v___y_931_);
lean_dec(v___y_931_);
return v_res_933_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16(lean_object* v_msg_934_, lean_object* v_declHint_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v___x_941_; lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_951_; 
v___x_941_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg(v_msg_934_, v_declHint_935_, v___y_939_);
v_a_942_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_951_ == 0)
{
v___x_944_ = v___x_941_;
v_isShared_945_ = v_isSharedCheck_951_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_941_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_951_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_946_ = l_Lean_unknownIdentifierMessageTag;
v___x_947_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v_a_942_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v___x_947_);
v___x_949_ = v___x_944_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_947_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_934_ = stack[0].m_obj;
lean_object* v_declHint_935_ = stack[1].m_obj;
lean_object* v___y_936_ = stack[2].m_obj;
lean_object* v___y_937_ = stack[3].m_obj;
lean_object* v___y_938_ = stack[4].m_obj;
lean_object* v___y_939_ = stack[5].m_obj;
lean_object* v_res_952_;
v_res_952_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16(v_msg_934_, v_declHint_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
stack->m_obj
 = v_res_952_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16___boxed(lean_object* v_msg_953_, lean_object* v_declHint_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16(v_msg_953_, v_declHint_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
return v_res_960_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg(lean_object* v_ref_961_, lean_object* v_msg_962_, lean_object* v_declHint_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___x_969_; lean_object* v_a_970_; lean_object* v___x_971_; 
v___x_969_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16(v_msg_962_, v_declHint_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref(v___x_969_);
v___x_971_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_ref_961_, v_a_970_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
return v___x_971_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_961_ = stack[0].m_obj;
lean_object* v_msg_962_ = stack[1].m_obj;
lean_object* v_declHint_963_ = stack[2].m_obj;
lean_object* v___y_964_ = stack[3].m_obj;
lean_object* v___y_965_ = stack[4].m_obj;
lean_object* v___y_966_ = stack[5].m_obj;
lean_object* v___y_967_ = stack[6].m_obj;
lean_object* v_res_972_;
v_res_972_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg(v_ref_961_, v_msg_962_, v_declHint_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
stack->m_obj
 = v_res_972_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg___boxed(lean_object* v_ref_973_, lean_object* v_msg_974_, lean_object* v_declHint_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg(v_ref_973_, v_msg_974_, v_declHint_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v_ref_973_);
return v_res_981_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__1(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__0));
v___x_984_ = l_Lean_stringToMessageData(v___x_983_);
return v___x_984_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__2));
v___x_987_ = l_Lean_stringToMessageData(v___x_986_);
return v___x_987_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg(lean_object* v_ref_988_, lean_object* v_constName_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; uint8_t v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_995_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__1);
v___x_996_ = 0;
lean_inc(v_constName_989_);
v___x_997_ = l_Lean_MessageData_ofConstName(v_constName_989_, v___x_996_);
v___x_998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_995_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__3);
v___x_1000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_998_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg(v_ref_988_, v___x_1000_, v_constName_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
return v___x_1001_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_988_ = stack[0].m_obj;
lean_object* v_constName_989_ = stack[1].m_obj;
lean_object* v___y_990_ = stack[2].m_obj;
lean_object* v___y_991_ = stack[3].m_obj;
lean_object* v___y_992_ = stack[4].m_obj;
lean_object* v___y_993_ = stack[5].m_obj;
lean_object* v_res_1002_;
v_res_1002_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg(v_ref_988_, v_constName_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
stack->m_obj
 = v_res_1002_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___boxed(lean_object* v_ref_1003_, lean_object* v_constName_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg(v_ref_1003_, v_constName_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v_ref_1003_);
return v_res_1010_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg(lean_object* v_constName_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_ref_1017_; lean_object* v___x_1018_; 
v_ref_1017_ = lean_ctor_get(v___y_1014_, 2);
v___x_1018_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg(v_ref_1017_, v_constName_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
return v___x_1018_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1011_ = stack[0].m_obj;
lean_object* v___y_1012_ = stack[1].m_obj;
lean_object* v___y_1013_ = stack[2].m_obj;
lean_object* v___y_1014_ = stack[3].m_obj;
lean_object* v___y_1015_ = stack[4].m_obj;
lean_object* v_res_1019_;
v_res_1019_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg(v_constName_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
stack->m_obj
 = v_res_1019_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg___boxed(lean_object* v_constName_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg(v_constName_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
return v_res_1026_;
}
}
lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6(lean_object* v_constName_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v___x_1033_; lean_object* v_env_1034_; uint8_t v___x_1035_; lean_object* v___x_1036_; 
v___x_1033_ = lean_st_ref_get(v___y_1031_);
v_env_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc_ref(v_env_1034_);
lean_dec(v___x_1033_);
v___x_1035_ = 0;
lean_inc(v_constName_1027_);
v___x_1036_ = l_Lean_Environment_find_x3f(v_env_1034_, v_constName_1027_, v___x_1035_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg(v_constName_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
return v___x_1037_;
}
else
{
lean_object* v_val_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec(v_constName_1027_);
v_val_1038_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1036_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_val_1038_);
lean_dec(v___x_1036_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
lean_ctor_set_tag(v___x_1040_, 0);
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_val_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1027_ = stack[0].m_obj;
lean_object* v___y_1028_ = stack[1].m_obj;
lean_object* v___y_1029_ = stack[2].m_obj;
lean_object* v___y_1030_ = stack[3].m_obj;
lean_object* v___y_1031_ = stack[4].m_obj;
lean_object* v_res_1046_;
v_res_1046_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6(v_constName_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
stack->m_obj
 = v_res_1046_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6___boxed(lean_object* v_constName_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6(v_constName_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
return v_res_1053_;
}
}
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs(lean_object* v_declName_1056_, lean_object* v_args_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1063_ = lean_array_get_size(v_args_1057_);
v___x_1064_ = lean_unsigned_to_nat(0u);
v___x_1065_ = lean_nat_dec_eq(v___x_1063_, v___x_1064_);
if (v___x_1065_ == 0)
{
lean_object* v___f_1066_; lean_object* v___x_1067_; 
lean_inc(v_declName_1056_);
v___f_1066_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1066_, 0, v___x_1064_);
lean_closure_set(v___f_1066_, 1, v_args_1057_);
lean_closure_set(v___f_1066_, 2, v_declName_1056_);
lean_closure_set(v___f_1066_, 3, v___x_1063_);
v___x_1067_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6(v_declName_1056_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1067_, 1);
v___x_1069_ = l_Lean_ConstantInfo_type(v_a_1068_);
lean_dec(v_a_1068_);
v___x_1070_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(v___x_1069_, v___f_1066_, v___x_1065_, v___x_1065_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
return v___x_1070_;
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_dec_ref(v___f_1066_);
v_a_1071_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1067_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1067_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
lean_dec_ref(v_args_1057_);
lean_dec(v_declName_1056_);
v___x_1079_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___closed__0));
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
return v___x_1080_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1056_ = stack[0].m_obj;
lean_object* v_args_1057_ = stack[1].m_obj;
lean_object* v_a_1058_ = stack[2].m_obj;
lean_object* v_a_1059_ = stack[3].m_obj;
lean_object* v_a_1060_ = stack[4].m_obj;
lean_object* v_a_1061_ = stack[5].m_obj;
lean_object* v_res_1081_;
v_res_1081_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs(v_declName_1056_, v_args_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
stack->m_obj
 = v_res_1081_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___boxed(lean_object* v_declName_1082_, lean_object* v_args_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs(v_declName_1082_, v_args_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
return v_res_1089_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0(size_t v_sz_1090_, size_t v_i_1091_, lean_object* v_bs_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg(v_sz_1090_, v_i_1091_, v_bs_1092_, v___y_1093_, v___y_1095_, v___y_1096_);
return v___x_1098_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1090_ = stack[0].m_num;
size_t v_i_1091_ = stack[1].m_num;
lean_object* v_bs_1092_ = stack[2].m_obj;
lean_object* v___y_1093_ = stack[3].m_obj;
lean_object* v___y_1094_ = stack[4].m_obj;
lean_object* v___y_1095_ = stack[5].m_obj;
lean_object* v___y_1096_ = stack[6].m_obj;
lean_object* v_res_1099_;
v_res_1099_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0(v_sz_1090_, v_i_1091_, v_bs_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
stack->m_obj
 = v_res_1099_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___boxed(lean_object* v_sz_1100_, lean_object* v_i_1101_, lean_object* v_bs_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
size_t v_sz_boxed_1108_; size_t v_i_boxed_1109_; lean_object* v_res_1110_; 
v_sz_boxed_1108_ = lean_unbox_usize(v_sz_1100_);
lean_dec(v_sz_1100_);
v_i_boxed_1109_ = lean_unbox_usize(v_i_1101_);
lean_dec(v_i_1101_);
v_res_1110_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0(v_sz_boxed_1108_, v_i_boxed_1109_, v_bs_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
return v_res_1110_;
}
}
lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2(lean_object* v_00_u03b1_1111_, lean_object* v_ref_1112_, lean_object* v_msg_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_ref_1112_, v_msg_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1112_ = stack[1].m_obj;
lean_object* v_msg_1113_ = stack[2].m_obj;
lean_object* v___y_1114_ = stack[3].m_obj;
lean_object* v___y_1115_ = stack[4].m_obj;
lean_object* v___y_1116_ = stack[5].m_obj;
lean_object* v___y_1117_ = stack[6].m_obj;
lean_object* v_res_1120_;
v_res_1120_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2(lean_box(0), v_ref_1112_, v_msg_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
stack->m_obj
 = v_res_1120_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___boxed(lean_object* v_00_u03b1_1121_, lean_object* v_ref_1122_, lean_object* v_msg_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2(v_00_u03b1_1121_, v_ref_1122_, v_msg_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v_ref_1122_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5(lean_object* v_n_1130_, lean_object* v_as_1131_, lean_object* v_lo_1132_, lean_object* v_hi_1133_, lean_object* v_w_1134_, lean_object* v_hlo_1135_, lean_object* v_hhi_1136_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(v_n_1130_, v_as_1131_, v_lo_1132_, v_hi_1133_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___boxed(lean_object* v_n_1138_, lean_object* v_as_1139_, lean_object* v_lo_1140_, lean_object* v_hi_1141_, lean_object* v_w_1142_, lean_object* v_hlo_1143_, lean_object* v_hhi_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5(v_n_1138_, v_as_1139_, v_lo_1140_, v_hi_1141_, v_w_1142_, v_hlo_1143_, v_hhi_1144_);
lean_dec(v_hi_1141_);
lean_dec(v_n_1138_);
return v_res_1145_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3(lean_object* v_00_u03b1_1146_, lean_object* v_msg_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg(v_msg_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
return v___x_1153_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1147_ = stack[1].m_obj;
lean_object* v___y_1148_ = stack[2].m_obj;
lean_object* v___y_1149_ = stack[3].m_obj;
lean_object* v___y_1150_ = stack[4].m_obj;
lean_object* v___y_1151_ = stack[5].m_obj;
lean_object* v_res_1154_;
v_res_1154_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3(lean_box(0), v_msg_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
stack->m_obj
 = v_res_1154_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1155_, lean_object* v_msg_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3(v_00_u03b1_1155_, v_msg_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8(lean_object* v_n_1163_, lean_object* v_lo_1164_, lean_object* v_hi_1165_, lean_object* v_hhi_1166_, lean_object* v_pivot_1167_, lean_object* v_as_1168_, lean_object* v_i_1169_, lean_object* v_k_1170_, lean_object* v_ilo_1171_, lean_object* v_ik_1172_, lean_object* v_w_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___redArg(v_hi_1165_, v_pivot_1167_, v_as_1168_, v_i_1169_, v_k_1170_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___boxed(lean_object* v_n_1175_, lean_object* v_lo_1176_, lean_object* v_hi_1177_, lean_object* v_hhi_1178_, lean_object* v_pivot_1179_, lean_object* v_as_1180_, lean_object* v_i_1181_, lean_object* v_k_1182_, lean_object* v_ilo_1183_, lean_object* v_ik_1184_, lean_object* v_w_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8(v_n_1175_, v_lo_1176_, v_hi_1177_, v_hhi_1178_, v_pivot_1179_, v_as_1180_, v_i_1181_, v_k_1182_, v_ilo_1183_, v_ik_1184_, v_w_1185_);
lean_dec(v_pivot_1179_);
lean_dec(v_hi_1177_);
lean_dec(v_lo_1176_);
lean_dec(v_n_1175_);
return v_res_1186_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10(lean_object* v_00_u03b1_1187_, lean_object* v_constName_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg(v_constName_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
return v___x_1194_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1188_ = stack[1].m_obj;
lean_object* v___y_1189_ = stack[2].m_obj;
lean_object* v___y_1190_ = stack[3].m_obj;
lean_object* v___y_1191_ = stack[4].m_obj;
lean_object* v___y_1192_ = stack[5].m_obj;
lean_object* v_res_1195_;
v_res_1195_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10(lean_box(0), v_constName_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
stack->m_obj
 = v_res_1195_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___boxed(lean_object* v_00_u03b1_1196_, lean_object* v_constName_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10(v_00_u03b1_1196_, v_constName_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
return v_res_1203_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14(lean_object* v_00_u03b1_1204_, lean_object* v_ref_1205_, lean_object* v_constName_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg(v_ref_1205_, v_constName_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
return v___x_1212_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1205_ = stack[1].m_obj;
lean_object* v_constName_1206_ = stack[2].m_obj;
lean_object* v___y_1207_ = stack[3].m_obj;
lean_object* v___y_1208_ = stack[4].m_obj;
lean_object* v___y_1209_ = stack[5].m_obj;
lean_object* v___y_1210_ = stack[6].m_obj;
lean_object* v_res_1213_;
v_res_1213_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14(lean_box(0), v_ref_1205_, v_constName_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
stack->m_obj
 = v_res_1213_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___boxed(lean_object* v_00_u03b1_1214_, lean_object* v_ref_1215_, lean_object* v_constName_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14(v_00_u03b1_1214_, v_ref_1215_, v_constName_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v_ref_1215_);
return v_res_1222_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15(lean_object* v_00_u03b1_1223_, lean_object* v_ref_1224_, lean_object* v_msg_1225_, lean_object* v_declHint_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg(v_ref_1224_, v_msg_1225_, v_declHint_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
return v___x_1232_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1224_ = stack[1].m_obj;
lean_object* v_msg_1225_ = stack[2].m_obj;
lean_object* v_declHint_1226_ = stack[3].m_obj;
lean_object* v___y_1227_ = stack[4].m_obj;
lean_object* v___y_1228_ = stack[5].m_obj;
lean_object* v___y_1229_ = stack[6].m_obj;
lean_object* v___y_1230_ = stack[7].m_obj;
lean_object* v_res_1233_;
v_res_1233_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15(lean_box(0), v_ref_1224_, v_msg_1225_, v_declHint_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
stack->m_obj
 = v_res_1233_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___boxed(lean_object* v_00_u03b1_1234_, lean_object* v_ref_1235_, lean_object* v_msg_1236_, lean_object* v_declHint_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15(v_00_u03b1_1234_, v_ref_1235_, v_msg_1236_, v_declHint_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v_ref_1235_);
return v_res_1243_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17(lean_object* v_msg_1244_, lean_object* v_declHint_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg(v_msg_1244_, v_declHint_1245_, v___y_1249_);
return v___x_1251_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1244_ = stack[0].m_obj;
lean_object* v_declHint_1245_ = stack[1].m_obj;
lean_object* v___y_1246_ = stack[2].m_obj;
lean_object* v___y_1247_ = stack[3].m_obj;
lean_object* v___y_1248_ = stack[4].m_obj;
lean_object* v___y_1249_ = stack[5].m_obj;
lean_object* v_res_1252_;
v_res_1252_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17(v_msg_1244_, v_declHint_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
stack->m_obj
 = v_res_1252_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___boxed(lean_object* v_msg_1253_, lean_object* v_declHint_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17(v_msg_1253_, v_declHint_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
return v_res_1260_;
}
}
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(lean_object* v_x_1261_, lean_object* v_x_1262_, lean_object* v_x_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = lean_box(0);
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1261_ = stack[0].m_obj;
lean_object* v_x_1262_ = stack[1].m_obj;
lean_object* v_x_1263_ = stack[2].m_obj;
lean_object* v___y_1264_ = stack[3].m_obj;
lean_object* v_res_1268_;
v_res_1268_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(v_x_1261_, v_x_1262_, v_x_1263_, v___y_1264_);
stack->m_obj
 = v_res_1268_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object* v_x_1269_, lean_object* v_x_1270_, lean_object* v_x_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(v_x_1269_, v_x_1270_, v_x_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v_x_1271_);
lean_dec_ref(v_x_1270_);
lean_dec(v_x_1269_);
return v_res_1274_;
}
}
uint8_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(lean_object* v_env_1275_, lean_object* v_n_1276_, lean_object* v_x_1277_){
_start:
{
uint8_t v___x_1278_; uint8_t v___x_1279_; 
v___x_1278_ = 1;
v___x_1279_ = l_Lean_Environment_contains(v_env_1275_, v_n_1276_, v___x_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1275_ = stack[0].m_obj;
lean_object* v_n_1276_ = stack[1].m_obj;
lean_object* v_x_1277_ = stack[2].m_obj;
uint8_t v_res_1280_;
v_res_1280_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(v_env_1275_, v_n_1276_, v_x_1277_);
stack->m_num = v_res_1280_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object* v_env_1281_, lean_object* v_n_1282_, lean_object* v_x_1283_){
_start:
{
uint8_t v_res_1284_; lean_object* v_r_1285_; 
v_res_1284_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(v_env_1281_, v_n_1282_, v_x_1283_);
lean_dec_ref(v_x_1283_);
v_r_1285_ = lean_box(v_res_1284_);
return v_r_1285_;
}
}
static uint64_t _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1292_; uint64_t v___x_1293_; 
v___x_1292_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_));
v___x_1293_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1292_);
return v___x_1293_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1294_ = lean_uint64_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1295_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_));
v___x_1296_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
lean_ctor_set_uint64(v___x_1296_, sizeof(void*)*1, v___x_1294_);
return v___x_1296_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0);
v___x_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
return v___x_1298_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1299_ = lean_box(1);
v___x_1300_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4);
v___x_1301_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v___x_1300_);
lean_ctor_set(v___x_1302_, 2, v___x_1299_);
return v___x_1302_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1305_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1306_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1307_ = lean_unsigned_to_nat(0u);
v___x_1308_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
lean_ctor_set(v___x_1308_, 2, v___x_1307_);
lean_ctor_set(v___x_1308_, 3, v___x_1307_);
lean_ctor_set(v___x_1308_, 4, v___x_1306_);
lean_ctor_set(v___x_1308_, 5, v___x_1306_);
lean_ctor_set(v___x_1308_, 6, v___x_1306_);
lean_ctor_set(v___x_1308_, 7, v___x_1306_);
lean_ctor_set(v___x_1308_, 8, v___x_1306_);
lean_ctor_set(v___x_1308_, 9, v___x_1306_);
lean_ctor_set(v___x_1308_, 10, v___x_1306_);
lean_ctor_set(v___x_1308_, 11, v___x_1305_);
return v___x_1308_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1310_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
lean_ctor_set(v___x_1310_, 2, v___x_1309_);
lean_ctor_set(v___x_1310_, 3, v___x_1309_);
lean_ctor_set(v___x_1310_, 4, v___x_1309_);
lean_ctor_set(v___x_1310_, 5, v___x_1309_);
return v___x_1310_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
lean_ctor_set(v___x_1312_, 2, v___x_1311_);
lean_ctor_set(v___x_1312_, 3, v___x_1311_);
lean_ctor_set(v___x_1312_, 4, v___x_1311_);
return v___x_1312_;
}
}
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(lean_object* v___x_1313_, lean_object* v_declName_1314_, lean_object* v_stx_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v_args_1321_; uint8_t v___x_1322_; uint8_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1319_ = lean_unsigned_to_nat(1u);
v___x_1320_ = l_Lean_Syntax_getArg(v_stx_1315_, v___x_1319_);
v_args_1321_ = l_Lean_Syntax_getArgs(v___x_1320_);
lean_dec(v___x_1320_);
v___x_1322_ = 0;
v___x_1323_ = 1;
v___x_1324_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1325_ = lean_unsigned_to_nat(0u);
v___x_1326_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4);
v___x_1327_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1328_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_));
v___x_1329_ = lean_box(0);
lean_inc(v___x_1313_);
v___x_1330_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1330_, 0, v___x_1324_);
lean_ctor_set(v___x_1330_, 1, v___x_1313_);
lean_ctor_set(v___x_1330_, 2, v___x_1327_);
lean_ctor_set(v___x_1330_, 3, v___x_1328_);
lean_ctor_set(v___x_1330_, 4, v___x_1329_);
lean_ctor_set(v___x_1330_, 5, v___x_1325_);
lean_ctor_set(v___x_1330_, 6, v___x_1329_);
lean_ctor_set_uint8(v___x_1330_, sizeof(void*)*7, v___x_1322_);
lean_ctor_set_uint8(v___x_1330_, sizeof(void*)*7 + 1, v___x_1322_);
lean_ctor_set_uint8(v___x_1330_, sizeof(void*)*7 + 2, v___x_1322_);
lean_ctor_set_uint8(v___x_1330_, sizeof(void*)*7 + 3, v___x_1323_);
v___x_1331_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1332_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1333_ = lean_obj_once(&l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_, &l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
v___x_1334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1331_);
lean_ctor_set(v___x_1334_, 1, v___x_1332_);
lean_ctor_set(v___x_1334_, 2, v___x_1313_);
lean_ctor_set(v___x_1334_, 3, v___x_1326_);
lean_ctor_set(v___x_1334_, 4, v___x_1333_);
v___x_1335_ = lean_st_mk_ref(v___x_1334_);
v___x_1336_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs(v_declName_1314_, v_args_1321_, v___x_1330_, v___x_1335_, v___y_1316_, v___y_1317_);
lean_dec_ref_known(v___x_1330_, 7);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1345_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1339_ = v___x_1336_;
v_isShared_1340_ = v_isSharedCheck_1345_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1336_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1345_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; lean_object* v___x_1343_; 
v___x_1341_ = lean_st_ref_get(v___x_1335_);
lean_dec(v___x_1335_);
lean_dec(v___x_1341_);
if (v_isShared_1340_ == 0)
{
v___x_1343_ = v___x_1339_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1337_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
else
{
lean_dec(v___x_1335_);
return v___x_1336_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1313_ = stack[0].m_obj;
lean_object* v_declName_1314_ = stack[1].m_obj;
lean_object* v_stx_1315_ = stack[2].m_obj;
lean_object* v___y_1316_ = stack[3].m_obj;
lean_object* v___y_1317_ = stack[4].m_obj;
lean_object* v_res_1346_;
v_res_1346_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(v___x_1313_, v_declName_1314_, v_stx_1315_, v___y_1316_, v___y_1317_);
stack->m_obj
 = v_res_1346_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object* v___x_1347_, lean_object* v_declName_1348_, lean_object* v_stx_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(v___x_1347_, v_declName_1348_, v_stx_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v_stx_1349_);
return v_res_1353_;
}
}
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_));
v___x_1380_ = l_Lean_registerParametricAttribute___redArg(v___x_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1381_;
v_res_1381_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1381_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(lean_object* v_a_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_();
return v_res_1383_;
}
}
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1(){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1386_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_));
v___x_1387_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1___closed__0));
v___x_1388_ = l_Lean_addBuiltinDocString(v___x_1386_, v___x_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1389_;
v_res_1389_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1();
stack->m_obj
 = v_res_1389_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1___boxed(lean_object* v_a_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1();
return v_res_1391_;
}
}
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3(){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1418_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_));
v___x_1419_ = ((lean_object*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__6));
v___x_1420_ = l_Lean_addBuiltinDeclarationRanges(v___x_1418_, v___x_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1421_;
v_res_1421_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3();
stack->m_obj
 = v_res_1421_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___boxed(lean_object* v_a_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3();
return v_res_1423_;
}
}
static lean_object* _init_l_Lean_Compiler_getSpecializationArgs_x3f___closed__0(void){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Array_instInhabited___redArg();
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getSpecializationArgs_x3f(lean_object* v_env_1425_, lean_object* v_declName_1426_){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1427_ = lean_obj_once(&l_Lean_Compiler_getSpecializationArgs_x3f___closed__0, &l_Lean_Compiler_getSpecializationArgs_x3f___closed__0_once, _init_l_Lean_Compiler_getSpecializationArgs_x3f___closed__0);
v___x_1428_ = l_Lean_Compiler_specializeAttr;
v___x_1429_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_1427_, v___x_1428_, v_env_1425_, v_declName_1426_);
return v___x_1429_;
}
}
uint8_t l_Lean_Compiler_hasSpecializeAttribute(lean_object* v_env_1430_, lean_object* v_declName_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_Compiler_getSpecializationArgs_x3f(v_env_1430_, v_declName_1431_);
if (lean_obj_tag(v___x_1432_) == 0)
{
uint8_t v___x_1433_; 
v___x_1433_ = 0;
return v___x_1433_;
}
else
{
uint8_t v___x_1434_; 
lean_dec_ref_known(v___x_1432_, 1);
v___x_1434_ = 1;
return v___x_1434_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_hasSpecializeAttribute_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1430_ = stack[0].m_obj;
lean_object* v_declName_1431_ = stack[1].m_obj;
uint8_t v_res_1435_;
v_res_1435_ = l_Lean_Compiler_hasSpecializeAttribute(v_env_1430_, v_declName_1431_);
stack->m_num = v_res_1435_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasSpecializeAttribute___boxed(lean_object* v_env_1436_, lean_object* v_declName_1437_){
_start:
{
uint8_t v_res_1438_; lean_object* v_r_1439_; 
v_res_1438_ = l_Lean_Compiler_hasSpecializeAttribute(v_env_1436_, v_declName_1437_);
v_r_1439_ = lean_box(v_res_1438_);
return v_r_1439_;
}
}
uint8_t l_Lean_Compiler_hasNospecializeAttribute(lean_object* v_env_1440_, lean_object* v_declName_1441_){
_start:
{
lean_object* v___x_1442_; uint8_t v___x_1443_; 
v___x_1442_ = l_Lean_Compiler_nospecializeAttr;
v___x_1443_ = l_Lean_TagAttribute_hasTag(v___x_1442_, v_env_1440_, v_declName_1441_);
return v___x_1443_;
}
}
LEAN_EXPORT void l_Lean_Compiler_hasNospecializeAttribute_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1440_ = stack[0].m_obj;
lean_object* v_declName_1441_ = stack[1].m_obj;
uint8_t v_res_1444_;
v_res_1444_ = l_Lean_Compiler_hasNospecializeAttribute(v_env_1440_, v_declName_1441_);
stack->m_num = v_res_1444_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasNospecializeAttribute___boxed(lean_object* v_env_1445_, lean_object* v_declName_1446_){
_start:
{
uint8_t v_res_1447_; lean_object* v_r_1448_; 
v_res_1447_ = l_Lean_Compiler_hasNospecializeAttribute(v_env_1445_, v_declName_1446_);
v_r_1448_ = lean_box(v_res_1447_);
return v_r_1448_;
}
}
uint8_t l_Lean_Compiler_hasWeakSpecializeAttribute(lean_object* v_env_1449_, lean_object* v_declName_1450_){
_start:
{
lean_object* v___x_1451_; uint8_t v___x_1452_; 
v___x_1451_ = l_Lean_Compiler_weakSpecializeAttr;
v___x_1452_ = l_Lean_TagAttribute_hasTag(v___x_1451_, v_env_1449_, v_declName_1450_);
return v___x_1452_;
}
}
LEAN_EXPORT void l_Lean_Compiler_hasWeakSpecializeAttribute_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1449_ = stack[0].m_obj;
lean_object* v_declName_1450_ = stack[1].m_obj;
uint8_t v_res_1453_;
v_res_1453_ = l_Lean_Compiler_hasWeakSpecializeAttribute(v_env_1449_, v_declName_1450_);
stack->m_num = v_res_1453_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_hasWeakSpecializeAttribute___boxed(lean_object* v_env_1454_, lean_object* v_declName_1455_){
_start:
{
uint8_t v_res_1456_; lean_object* v_r_1457_; 
v_res_1456_ = l_Lean_Compiler_hasWeakSpecializeAttribute(v_env_1454_, v_declName_1455_);
v_r_1457_ = lean_box(v_res_1456_);
return v_r_1457_;
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
