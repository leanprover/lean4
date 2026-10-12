// Lean compiler output
// Module: Lean.Compiler.ExternAttr
// Imports: public import Lean.ProjFns public import Lean.Attributes import Init.Data.String.Lemmas.Order import Init.Data.String.OrderInstances import Init.Data.Order.Lemmas
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
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_intersperseTR___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_List_getD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecls(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
uint8_t l_Lean_Environment_isConstructor(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_string_hash(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_registerParametricAttribute___redArg(lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_adhoc_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_adhoc_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_inline_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_inline_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_standard_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_standard_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_opaque_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_opaque_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqExternEntry_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqExternEntry_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqExternEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExternEntry_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqExternEntry___closed__0 = (const lean_object*)&l_Lean_instBEqExternEntry___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqExternEntry = (const lean_object*)&l_Lean_instBEqExternEntry___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_instHashableExternEntry_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableExternEntry_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableExternEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExternEntry_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableExternEntry___closed__0 = (const lean_object*)&l_Lean_instHashableExternEntry___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableExternEntry = (const lean_object*)&l_Lean_instHashableExternEntry___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedExternAttrData_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedExternAttrData;
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqExternAttrData_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqExternAttrData_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqExternAttrData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExternAttrData_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqExternAttrData___closed__0 = (const lean_object*)&l_Lean_instBEqExternAttrData___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqExternAttrData = (const lean_object*)&l_Lean_instBEqExternAttrData___closed__0_value;
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_instHashableExternAttrData_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableExternAttrData_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableExternAttrData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExternAttrData_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableExternAttrData___closed__0 = (const lean_object*)&l_Lean_instHashableExternAttrData___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableExternAttrData = (const lean_object*)&l_Lean_instHashableExternAttrData___closed__0_value;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "string literal expected"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 186, 94, 176, 136, 38, 52, 11)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__0 = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3_value)}};
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__1 = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2 = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "externAttr"};
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 152, 26, 79, 119, 188, 216, 230)}};
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "extern"};
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(146, 128, 231, 207, 24, 58, 115, 13)}};
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "builtin and foreign functions"};
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_externAttr;
LEAN_EXPORT lean_object* l_Lean_getExternAttrData_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_expandExternPatternAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_expandExternPatternAux___closed__0 = (const lean_object*)&l_Lean_expandExternPatternAux___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandExternPattern(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandExternPattern___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkSimpleFnCall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_mkSimpleFnCall___closed__0 = (const lean_object*)&l_Lean_mkSimpleFnCall___closed__0_value;
static const lean_string_object l_Lean_mkSimpleFnCall___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_mkSimpleFnCall___closed__1 = (const lean_object*)&l_Lean_mkSimpleFnCall___closed__1_value;
static const lean_string_object l_Lean_mkSimpleFnCall___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_mkSimpleFnCall___closed__2 = (const lean_object*)&l_Lean_mkSimpleFnCall___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_mkSimpleFnCall(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isExtern(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isExtern___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isExternC(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isExternC___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternNameFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternNameFor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_ExternEntry_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
switch(lean_obj_tag(v_t_5_))
{
case 0:
{
lean_object* v_backend_7_; lean_object* v___x_8_; 
v_backend_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_backend_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_backend_7_);
return v___x_8_;
}
case 3:
{
return v_k_6_;
}
default: 
{
lean_object* v_backend_9_; lean_object* v_pattern_10_; lean_object* v___x_11_; 
v_backend_9_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_backend_9_);
v_pattern_10_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_pattern_10_);
lean_dec(v_t_5_);
v___x_11_ = lean_apply_2(v_k_6_, v_backend_9_, v_pattern_10_);
return v___x_11_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, lean_object* v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_14_, v_k_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_ExternEntry_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_20_, v_h_21_, v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_adhoc_elim___redArg(lean_object* v_t_24_, lean_object* v_adhoc_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_24_, v_adhoc_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_adhoc_elim(lean_object* v_motive_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_adhoc_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_28_, v_adhoc_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_inline_elim___redArg(lean_object* v_t_32_, lean_object* v_inline_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_32_, v_inline_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_inline_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_inline_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_36_, v_inline_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_standard_elim___redArg(lean_object* v_t_40_, lean_object* v_standard_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_40_, v_standard_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_standard_elim(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_standard_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_44_, v_standard_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_opaque_elim___redArg(lean_object* v_t_48_, lean_object* v_opaque_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_48_, v_opaque_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_opaque_elim(lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_opaque_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_52_, v_opaque_54_);
return v___x_55_;
}
}
uint8_t l_Lean_instBEqExternEntry_beq(lean_object* v_x_56_, lean_object* v_x_57_){
_start:
{
lean_object* v_a_59_; lean_object* v_a_60_; lean_object* v_b_61_; lean_object* v_b_62_; 
switch(lean_obj_tag(v_x_56_))
{
case 0:
{
if (lean_obj_tag(v_x_57_) == 0)
{
lean_object* v_backend_65_; lean_object* v_backend_66_; uint8_t v___x_67_; 
v_backend_65_ = lean_ctor_get(v_x_56_, 0);
v_backend_66_ = lean_ctor_get(v_x_57_, 0);
v___x_67_ = lean_name_eq(v_backend_65_, v_backend_66_);
return v___x_67_;
}
else
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
case 1:
{
if (lean_obj_tag(v_x_57_) == 1)
{
lean_object* v_backend_69_; lean_object* v_pattern_70_; lean_object* v_backend_71_; lean_object* v_pattern_72_; 
v_backend_69_ = lean_ctor_get(v_x_56_, 0);
v_pattern_70_ = lean_ctor_get(v_x_56_, 1);
v_backend_71_ = lean_ctor_get(v_x_57_, 0);
v_pattern_72_ = lean_ctor_get(v_x_57_, 1);
v_a_59_ = v_backend_69_;
v_a_60_ = v_pattern_70_;
v_b_61_ = v_backend_71_;
v_b_62_ = v_pattern_72_;
goto v___jp_58_;
}
else
{
uint8_t v___x_73_; 
v___x_73_ = 0;
return v___x_73_;
}
}
case 2:
{
if (lean_obj_tag(v_x_57_) == 2)
{
lean_object* v_backend_74_; lean_object* v_fn_75_; lean_object* v_backend_76_; lean_object* v_fn_77_; 
v_backend_74_ = lean_ctor_get(v_x_56_, 0);
v_fn_75_ = lean_ctor_get(v_x_56_, 1);
v_backend_76_ = lean_ctor_get(v_x_57_, 0);
v_fn_77_ = lean_ctor_get(v_x_57_, 1);
v_a_59_ = v_backend_74_;
v_a_60_ = v_fn_75_;
v_b_61_ = v_backend_76_;
v_b_62_ = v_fn_77_;
goto v___jp_58_;
}
else
{
uint8_t v___x_78_; 
v___x_78_ = 0;
return v___x_78_;
}
}
default: 
{
if (lean_obj_tag(v_x_57_) == 3)
{
uint8_t v___x_79_; 
v___x_79_ = 1;
return v___x_79_;
}
else
{
uint8_t v___x_80_; 
v___x_80_ = 0;
return v___x_80_;
}
}
}
v___jp_58_:
{
uint8_t v___x_63_; 
v___x_63_ = lean_name_eq(v_a_59_, v_b_61_);
if (v___x_63_ == 0)
{
return v___x_63_;
}
else
{
uint8_t v___x_64_; 
v___x_64_ = lean_string_dec_eq(v_a_60_, v_b_62_);
return v___x_64_;
}
}
}
}
LEAN_EXPORT void l_Lean_instBEqExternEntry_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_56_ = stack[0].m_obj;
lean_object* v_x_57_ = stack[1].m_obj;
uint8_t v_res_81_;
v_res_81_ = l_Lean_instBEqExternEntry_beq(v_x_56_, v_x_57_);
stack->m_num = v_res_81_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqExternEntry_beq___boxed(lean_object* v_x_82_, lean_object* v_x_83_){
_start:
{
uint8_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = l_Lean_instBEqExternEntry_beq(v_x_82_, v_x_83_);
lean_dec(v_x_83_);
lean_dec(v_x_82_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
uint64_t l_Lean_instHashableExternEntry_hash(lean_object* v_x_88_){
_start:
{
switch(lean_obj_tag(v_x_88_))
{
case 0:
{
lean_object* v_backend_89_; uint64_t v___x_90_; 
v_backend_89_ = lean_ctor_get(v_x_88_, 0);
v___x_90_ = 0ULL;
if (lean_obj_tag(v_backend_89_) == 0)
{
uint64_t v___x_91_; 
v___x_91_ = 8934034000889494153ULL;
return v___x_91_;
}
else
{
uint64_t v_hash_92_; uint64_t v___x_93_; 
v_hash_92_ = lean_ctor_get_uint64(v_backend_89_, sizeof(void*)*2);
v___x_93_ = lean_uint64_mix_hash(v___x_90_, v_hash_92_);
return v___x_93_;
}
}
case 1:
{
lean_object* v_backend_94_; lean_object* v_pattern_95_; uint64_t v___x_96_; uint64_t v___y_98_; 
v_backend_94_ = lean_ctor_get(v_x_88_, 0);
v_pattern_95_ = lean_ctor_get(v_x_88_, 1);
v___x_96_ = 1ULL;
if (lean_obj_tag(v_backend_94_) == 0)
{
uint64_t v___x_102_; 
v___x_102_ = 1723ULL;
v___y_98_ = v___x_102_;
goto v___jp_97_;
}
else
{
uint64_t v_hash_103_; 
v_hash_103_ = lean_ctor_get_uint64(v_backend_94_, sizeof(void*)*2);
v___y_98_ = v_hash_103_;
goto v___jp_97_;
}
v___jp_97_:
{
uint64_t v___x_99_; uint64_t v___x_100_; uint64_t v___x_101_; 
v___x_99_ = lean_uint64_mix_hash(v___x_96_, v___y_98_);
v___x_100_ = lean_string_hash(v_pattern_95_);
v___x_101_ = lean_uint64_mix_hash(v___x_99_, v___x_100_);
return v___x_101_;
}
}
case 2:
{
lean_object* v_backend_104_; lean_object* v_fn_105_; uint64_t v___x_106_; uint64_t v___y_108_; 
v_backend_104_ = lean_ctor_get(v_x_88_, 0);
v_fn_105_ = lean_ctor_get(v_x_88_, 1);
v___x_106_ = 2ULL;
if (lean_obj_tag(v_backend_104_) == 0)
{
uint64_t v___x_112_; 
v___x_112_ = 1723ULL;
v___y_108_ = v___x_112_;
goto v___jp_107_;
}
else
{
uint64_t v_hash_113_; 
v_hash_113_ = lean_ctor_get_uint64(v_backend_104_, sizeof(void*)*2);
v___y_108_ = v_hash_113_;
goto v___jp_107_;
}
v___jp_107_:
{
uint64_t v___x_109_; uint64_t v___x_110_; uint64_t v___x_111_; 
v___x_109_ = lean_uint64_mix_hash(v___x_106_, v___y_108_);
v___x_110_ = lean_string_hash(v_fn_105_);
v___x_111_ = lean_uint64_mix_hash(v___x_109_, v___x_110_);
return v___x_111_;
}
}
default: 
{
uint64_t v___x_114_; 
v___x_114_ = 3ULL;
return v___x_114_;
}
}
}
}
LEAN_EXPORT void l_Lean_instHashableExternEntry_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_88_ = stack[0].m_obj;
uint64_t v_res_115_;
v_res_115_ = l_Lean_instHashableExternEntry_hash(v_x_88_);
stack->m_num = v_res_115_;
}
LEAN_EXPORT lean_object* l_Lean_instHashableExternEntry_hash___boxed(lean_object* v_x_116_){
_start:
{
uint64_t v_res_117_; lean_object* v_r_118_; 
v_res_117_ = l_Lean_instHashableExternEntry_hash(v_x_116_);
lean_dec(v_x_116_);
v_r_118_ = lean_box_uint64(v_res_117_);
return v_r_118_;
}
}
static lean_object* _init_l_Lean_instInhabitedExternAttrData_default(void){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lean_box(0);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_instInhabitedExternAttrData(void){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_box(0);
return v___x_122_;
}
}
uint8_t l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0(lean_object* v_x_123_, lean_object* v_x_124_){
_start:
{
if (lean_obj_tag(v_x_123_) == 0)
{
if (lean_obj_tag(v_x_124_) == 0)
{
uint8_t v___x_125_; 
v___x_125_ = 1;
return v___x_125_;
}
else
{
uint8_t v___x_126_; 
v___x_126_ = 0;
return v___x_126_;
}
}
else
{
if (lean_obj_tag(v_x_124_) == 0)
{
uint8_t v___x_127_; 
v___x_127_ = 0;
return v___x_127_;
}
else
{
lean_object* v_head_128_; lean_object* v_tail_129_; lean_object* v_head_130_; lean_object* v_tail_131_; uint8_t v___x_132_; 
v_head_128_ = lean_ctor_get(v_x_123_, 0);
v_tail_129_ = lean_ctor_get(v_x_123_, 1);
v_head_130_ = lean_ctor_get(v_x_124_, 0);
v_tail_131_ = lean_ctor_get(v_x_124_, 1);
v___x_132_ = l_Lean_instBEqExternEntry_beq(v_head_128_, v_head_130_);
if (v___x_132_ == 0)
{
return v___x_132_;
}
else
{
v_x_123_ = v_tail_129_;
v_x_124_ = v_tail_131_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_123_ = stack[0].m_obj;
lean_object* v_x_124_ = stack[1].m_obj;
uint8_t v_res_134_;
v_res_134_ = l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0(v_x_123_, v_x_124_);
stack->m_num = v_res_134_;
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0___boxed(lean_object* v_x_135_, lean_object* v_x_136_){
_start:
{
uint8_t v_res_137_; lean_object* v_r_138_; 
v_res_137_ = l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0(v_x_135_, v_x_136_);
lean_dec(v_x_136_);
lean_dec(v_x_135_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
uint8_t l_Lean_instBEqExternAttrData_beq(lean_object* v_x_139_, lean_object* v_x_140_){
_start:
{
uint8_t v___x_141_; 
v___x_141_ = l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0(v_x_139_, v_x_140_);
return v___x_141_;
}
}
LEAN_EXPORT void l_Lean_instBEqExternAttrData_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_139_ = stack[0].m_obj;
lean_object* v_x_140_ = stack[1].m_obj;
uint8_t v_res_142_;
v_res_142_ = l_Lean_instBEqExternAttrData_beq(v_x_139_, v_x_140_);
stack->m_num = v_res_142_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqExternAttrData_beq___boxed(lean_object* v_x_143_, lean_object* v_x_144_){
_start:
{
uint8_t v_res_145_; lean_object* v_r_146_; 
v_res_145_ = l_Lean_instBEqExternAttrData_beq(v_x_143_, v_x_144_);
lean_dec(v_x_144_);
lean_dec(v_x_143_);
v_r_146_ = lean_box(v_res_145_);
return v_r_146_;
}
}
uint64_t l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0(uint64_t v_x_149_, lean_object* v_x_150_){
_start:
{
if (lean_obj_tag(v_x_150_) == 0)
{
return v_x_149_;
}
else
{
lean_object* v_head_151_; lean_object* v_tail_152_; uint64_t v___x_153_; uint64_t v___x_154_; 
v_head_151_ = lean_ctor_get(v_x_150_, 0);
v_tail_152_ = lean_ctor_get(v_x_150_, 1);
v___x_153_ = l_Lean_instHashableExternEntry_hash(v_head_151_);
v___x_154_ = lean_uint64_mix_hash(v_x_149_, v___x_153_);
v_x_149_ = v___x_154_;
v_x_150_ = v_tail_152_;
goto _start;
}
}
}
LEAN_EXPORT void l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_x_149_ = stack[0].m_num;
lean_object* v_x_150_ = stack[1].m_obj;
uint64_t v_res_156_;
v_res_156_ = l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0(v_x_149_, v_x_150_);
stack->m_num = v_res_156_;
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0___boxed(lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
uint64_t v_x_57__boxed_159_; uint64_t v_res_160_; lean_object* v_r_161_; 
v_x_57__boxed_159_ = lean_unbox_uint64(v_x_157_);
lean_dec_ref(v_x_157_);
v_res_160_ = l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0(v_x_57__boxed_159_, v_x_158_);
lean_dec(v_x_158_);
v_r_161_ = lean_box_uint64(v_res_160_);
return v_r_161_;
}
}
uint64_t l_Lean_instHashableExternAttrData_hash(lean_object* v_x_162_){
_start:
{
uint64_t v___x_163_; uint64_t v___x_164_; uint64_t v___x_165_; uint64_t v___x_166_; 
v___x_163_ = 0ULL;
v___x_164_ = 7ULL;
v___x_165_ = l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0(v___x_164_, v_x_162_);
v___x_166_ = lean_uint64_mix_hash(v___x_163_, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT void l_Lean_instHashableExternAttrData_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_162_ = stack[0].m_obj;
uint64_t v_res_167_;
v_res_167_ = l_Lean_instHashableExternAttrData_hash(v_x_162_);
stack->m_num = v_res_167_;
}
LEAN_EXPORT lean_object* l_Lean_instHashableExternAttrData_hash___boxed(lean_object* v_x_168_){
_start:
{
uint64_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_Lean_instHashableExternAttrData_hash(v_x_168_);
lean_dec(v_x_168_);
v_r_170_ = lean_box_uint64(v_res_169_);
return v_r_170_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_173_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__0);
v___x_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
return v___x_175_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_176_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_177_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1);
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
lean_ctor_set(v___x_179_, 2, v___x_178_);
lean_ctor_set(v___x_179_, 3, v___x_178_);
lean_ctor_set(v___x_179_, 4, v___x_177_);
lean_ctor_set(v___x_179_, 5, v___x_177_);
lean_ctor_set(v___x_179_, 6, v___x_177_);
lean_ctor_set(v___x_179_, 7, v___x_177_);
lean_ctor_set(v___x_179_, 8, v___x_177_);
lean_ctor_set(v___x_179_, 9, v___x_177_);
lean_ctor_set(v___x_179_, 10, v___x_177_);
lean_ctor_set(v___x_179_, 11, v___x_176_);
return v___x_179_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_unsigned_to_nat(32u);
v___x_181_ = lean_mk_empty_array_with_capacity(v___x_180_);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_183_ = ((size_t)5ULL);
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = lean_unsigned_to_nat(32u);
v___x_186_ = lean_mk_empty_array_with_capacity(v___x_185_);
v___x_187_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3);
v___x_188_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_186_);
lean_ctor_set(v___x_188_, 2, v___x_184_);
lean_ctor_set(v___x_188_, 3, v___x_184_);
lean_ctor_set_usize(v___x_188_, 4, v___x_183_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_189_ = lean_box(1);
v___x_190_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4);
v___x_191_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1);
v___x_192_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_190_);
lean_ctor_set(v___x_192_, 2, v___x_189_);
return v___x_192_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1(lean_object* v_msgData_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v___x_197_; lean_object* v_toCold_198_; lean_object* v_env_199_; lean_object* v_options_200_; uint8_t v___x_201_; lean_object* v_env_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_197_ = lean_st_ref_get(v___y_195_);
v_toCold_198_ = lean_ctor_get(v___y_194_, 0);
v_env_199_ = lean_ctor_get(v___x_197_, 0);
lean_inc_ref(v_env_199_);
lean_dec(v___x_197_);
v_options_200_ = lean_ctor_get(v_toCold_198_, 2);
v___x_201_ = 0;
v_env_202_ = l_Lean_Environment_setRecordingDeps(v_env_199_, v___x_201_);
v___x_203_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2);
v___x_204_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_200_);
v___x_205_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_205_, 0, v_env_202_);
lean_ctor_set(v___x_205_, 1, v___x_203_);
lean_ctor_set(v___x_205_, 2, v___x_204_);
lean_ctor_set(v___x_205_, 3, v_options_200_);
v___x_206_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v_msgData_193_);
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_193_ = stack[0].m_obj;
lean_object* v___y_194_ = stack[1].m_obj;
lean_object* v___y_195_ = stack[2].m_obj;
lean_object* v_res_208_;
v_res_208_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1(v_msgData_193_, v___y_194_, v___y_195_);
stack->m_obj
 = v_res_208_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1(v_msgData_209_, v___y_210_, v___y_211_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
return v_res_213_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(lean_object* v_msg_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_ref_218_; lean_object* v___x_219_; lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_228_; 
v_ref_218_ = lean_ctor_get(v___y_215_, 2);
v___x_219_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1(v_msg_214_, v___y_215_, v___y_216_);
v_a_220_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_228_ == 0)
{
v___x_222_ = v___x_219_;
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_226_; 
lean_inc(v_ref_218_);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v_ref_218_);
lean_ctor_set(v___x_224_, 1, v_a_220_);
if (v_isShared_223_ == 0)
{
lean_ctor_set_tag(v___x_222_, 1);
lean_ctor_set(v___x_222_, 0, v___x_224_);
v___x_226_ = v___x_222_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_214_ = stack[0].m_obj;
lean_object* v___y_215_ = stack[1].m_obj;
lean_object* v___y_216_ = stack[2].m_obj;
lean_object* v_res_229_;
v_res_229_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_214_, v___y_215_, v___y_216_);
stack->m_obj
 = v_res_229_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg___boxed(lean_object* v_msg_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_230_, v___y_231_, v___y_232_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
return v_res_234_;
}
}
lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(lean_object* v_ref_235_, lean_object* v_msg_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_toCold_240_; lean_object* v_currRecDepth_241_; lean_object* v_ref_242_; uint16_t v_optionFlags_243_; uint8_t v_suppressElabErrors_244_; uint8_t v_isRecordingDeps_245_; lean_object* v_ref_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_toCold_240_ = lean_ctor_get(v___y_237_, 0);
v_currRecDepth_241_ = lean_ctor_get(v___y_237_, 1);
v_ref_242_ = lean_ctor_get(v___y_237_, 2);
v_optionFlags_243_ = lean_ctor_get_uint16(v___y_237_, sizeof(void*)*3);
v_suppressElabErrors_244_ = lean_ctor_get_uint8(v___y_237_, sizeof(void*)*3 + 2);
v_isRecordingDeps_245_ = lean_ctor_get_uint8(v___y_237_, sizeof(void*)*3 + 3);
v_ref_246_ = l_Lean_replaceRef(v_ref_235_, v_ref_242_);
lean_inc(v_currRecDepth_241_);
lean_inc_ref(v_toCold_240_);
v___x_247_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_247_, 0, v_toCold_240_);
lean_ctor_set(v___x_247_, 1, v_currRecDepth_241_);
lean_ctor_set(v___x_247_, 2, v_ref_246_);
lean_ctor_set_uint16(v___x_247_, sizeof(void*)*3, v_optionFlags_243_);
lean_ctor_set_uint8(v___x_247_, sizeof(void*)*3 + 2, v_suppressElabErrors_244_);
lean_ctor_set_uint8(v___x_247_, sizeof(void*)*3 + 3, v_isRecordingDeps_245_);
v___x_248_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_236_, v___x_247_, v___y_238_);
lean_dec_ref_known(v___x_247_, 3);
return v___x_248_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_235_ = stack[0].m_obj;
lean_object* v_msg_236_ = stack[1].m_obj;
lean_object* v___y_237_ = stack[2].m_obj;
lean_object* v___y_238_ = stack[3].m_obj;
lean_object* v_res_249_;
v_res_249_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v_ref_235_, v_msg_236_, v___y_237_, v___y_238_);
stack->m_obj
 = v_res_249_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg___boxed(lean_object* v_ref_250_, lean_object* v_msg_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v_ref_250_, v_msg_251_, v___y_252_, v___y_253_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v_ref_250_);
return v_res_255_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__0));
v___x_258_ = l_Lean_stringToMessageData(v___x_257_);
return v___x_258_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(lean_object* v_as_262_, size_t v_sz_263_, size_t v_i_264_, lean_object* v_b_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_a_270_; uint8_t v___x_274_; 
v___x_274_ = lean_usize_dec_lt(v_i_264_, v_sz_263_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; 
v___x_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_275_, 0, v_b_265_);
return v___x_275_;
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v_a_278_; lean_object* v___y_280_; lean_object* v_str_281_; lean_object* v___y_289_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_276_ = lean_unsigned_to_nat(1u);
v___x_277_ = lean_unsigned_to_nat(0u);
v_a_278_ = lean_array_uget_borrowed(v_as_262_, v_i_264_);
v___x_305_ = l_Lean_Syntax_getArg(v_a_278_, v___x_277_);
v___x_306_ = l_Lean_Syntax_isNone(v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = l_Lean_Syntax_getArg(v___x_305_, v___x_277_);
lean_dec(v___x_305_);
v___x_308_ = l_Lean_Syntax_getId(v___x_307_);
lean_dec(v___x_307_);
v___y_289_ = v___x_308_;
goto v___jp_288_;
}
else
{
lean_object* v___x_309_; 
lean_dec(v___x_305_);
v___x_309_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
v___y_289_ = v___x_309_;
goto v___jp_288_;
}
v___jp_279_:
{
lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_282_ = l_Lean_Syntax_getArg(v_a_278_, v___x_276_);
v___x_283_ = l_Lean_Syntax_isNone(v___x_282_);
lean_dec(v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_284_, 0, v___y_280_);
lean_ctor_set(v___x_284_, 1, v_str_281_);
v___x_285_ = lean_array_push(v_b_265_, v___x_284_);
v_a_270_ = v___x_285_;
goto v___jp_269_;
}
else
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_286_, 0, v___y_280_);
lean_ctor_set(v___x_286_, 1, v_str_281_);
v___x_287_ = lean_array_push(v_b_265_, v___x_286_);
v_a_270_ = v___x_287_;
goto v___jp_269_;
}
}
v___jp_288_:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_290_ = lean_unsigned_to_nat(2u);
v___x_291_ = l_Lean_Syntax_getArg(v_a_278_, v___x_290_);
v___x_292_ = l_Lean_Syntax_isStrLit_x3f(v___x_291_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1);
v___x_294_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v___x_291_, v___x_293_, v___y_266_, v___y_267_);
lean_dec(v___x_291_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_295_);
lean_dec_ref_known(v___x_294_, 1);
v___y_280_ = v___y_289_;
v_str_281_ = v_a_295_;
goto v___jp_279_;
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
lean_dec(v___y_289_);
lean_dec_ref(v_b_265_);
v_a_296_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_294_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_294_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
else
{
lean_object* v_val_304_; 
lean_dec(v___x_291_);
v_val_304_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_val_304_);
lean_dec_ref_known(v___x_292_, 1);
v___y_280_ = v___y_289_;
v_str_281_ = v_val_304_;
goto v___jp_279_;
}
}
}
v___jp_269_:
{
size_t v___x_271_; size_t v___x_272_; 
v___x_271_ = ((size_t)1ULL);
v___x_272_ = lean_usize_add(v_i_264_, v___x_271_);
v_i_264_ = v___x_272_;
v_b_265_ = v_a_270_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_262_ = stack[0].m_obj;
size_t v_sz_263_ = stack[1].m_num;
size_t v_i_264_ = stack[2].m_num;
lean_object* v_b_265_ = stack[3].m_obj;
lean_object* v___y_266_ = stack[4].m_obj;
lean_object* v___y_267_ = stack[5].m_obj;
lean_object* v_res_310_;
v_res_310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(v_as_262_, v_sz_263_, v_i_264_, v_b_265_, v___y_266_, v___y_267_);
stack->m_obj
 = v_res_310_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___boxed(lean_object* v_as_311_, lean_object* v_sz_312_, lean_object* v_i_313_, lean_object* v_b_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
size_t v_sz_boxed_318_; size_t v_i_boxed_319_; lean_object* v_res_320_; 
v_sz_boxed_318_ = lean_unbox_usize(v_sz_312_);
lean_dec(v_sz_312_);
v_i_boxed_319_ = lean_unbox_usize(v_i_313_);
lean_dec(v_i_313_);
v_res_320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(v_as_311_, v_sz_boxed_318_, v_i_boxed_319_, v_b_314_, v___y_315_, v___y_316_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec_ref(v_as_311_);
return v_res_320_;
}
}
lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(lean_object* v_stx_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v_entriesStx_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_332_ = lean_unsigned_to_nat(1u);
v___x_333_ = l_Lean_Syntax_getArg(v_stx_328_, v___x_332_);
v_entriesStx_334_ = l_Lean_Syntax_getArgs(v___x_333_);
lean_dec(v___x_333_);
v___x_335_ = lean_array_get_size(v_entriesStx_334_);
v___x_336_ = lean_unsigned_to_nat(0u);
v___x_337_ = lean_nat_dec_eq(v___x_335_, v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v_entries_338_; size_t v_sz_339_; size_t v___x_340_; lean_object* v___x_341_; 
v_entries_338_ = ((lean_object*)(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__0));
v_sz_339_ = lean_array_size(v_entriesStx_334_);
v___x_340_ = ((size_t)0ULL);
v___x_341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(v_entriesStx_334_, v_sz_339_, v___x_340_, v_entries_338_, v_a_329_, v_a_330_);
lean_dec_ref(v_entriesStx_334_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_350_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_350_ == 0)
{
v___x_344_ = v___x_341_;
v_isShared_345_ = v_isSharedCheck_350_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_350_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; lean_object* v___x_348_; 
v___x_346_ = lean_array_to_list(v_a_342_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_346_);
v___x_348_ = v___x_344_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
v_a_351_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_341_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_341_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; 
lean_dec_ref(v_entriesStx_334_);
v___x_359_ = ((lean_object*)(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2));
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_328_ = stack[0].m_obj;
lean_object* v_a_329_ = stack[1].m_obj;
lean_object* v_a_330_ = stack[2].m_obj;
lean_object* v_res_361_;
v_res_361_ = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(v_stx_328_, v_a_329_, v_a_330_);
stack->m_obj
 = v_res_361_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___boxed(lean_object* v_stx_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(v_stx_362_, v_a_363_, v_a_364_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_stx_362_);
return v_res_366_;
}
}
lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(lean_object* v_00_u03b1_367_, lean_object* v_ref_368_, lean_object* v_msg_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v_ref_368_, v_msg_369_, v___y_370_, v___y_371_);
return v___x_373_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_368_ = stack[1].m_obj;
lean_object* v_msg_369_ = stack[2].m_obj;
lean_object* v___y_370_ = stack[3].m_obj;
lean_object* v___y_371_ = stack[4].m_obj;
lean_object* v_res_374_;
v_res_374_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(lean_box(0), v_ref_368_, v_msg_369_, v___y_370_, v___y_371_);
stack->m_obj
 = v_res_374_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___boxed(lean_object* v_00_u03b1_375_, lean_object* v_ref_376_, lean_object* v_msg_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(v_00_u03b1_375_, v_ref_376_, v_msg_377_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v_ref_376_);
return v_res_381_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0(lean_object* v_00_u03b1_382_, lean_object* v_msg_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_383_, v___y_384_, v___y_385_);
return v___x_387_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_383_ = stack[1].m_obj;
lean_object* v___y_384_ = stack[2].m_obj;
lean_object* v___y_385_ = stack[3].m_obj;
lean_object* v_res_388_;
v_res_388_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0(lean_box(0), v_msg_383_, v___y_384_, v___y_385_);
stack->m_obj
 = v_res_388_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___boxed(lean_object* v_00_u03b1_389_, lean_object* v_msg_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0(v_00_u03b1_389_, v_msg_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
return v_res_394_;
}
}
lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(lean_object* v_x_395_, lean_object* v_stx_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(v_stx_396_, v___y_397_, v___y_398_);
return v___x_400_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_x_395_ = stack[0].m_obj;
lean_object* v_stx_396_ = stack[1].m_obj;
lean_object* v___y_397_ = stack[2].m_obj;
lean_object* v___y_398_ = stack[3].m_obj;
lean_object* v_res_401_;
v_res_401_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v_x_395_, v_stx_396_, v___y_397_, v___y_398_);
stack->m_obj
 = v_res_401_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v_x_402_, lean_object* v_stx_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v_x_402_, v_stx_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v_stx_403_);
lean_dec(v_x_402_);
return v_res_407_;
}
}
lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(lean_object* v_declName_408_, lean_object* v_externAttrData_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
uint8_t v___y_414_; lean_object* v___x_419_; lean_object* v_env_420_; uint8_t v___y_422_; uint8_t v___x_437_; 
v___x_419_ = lean_st_ref_get(v___y_411_);
v_env_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc_ref_n(v_env_420_, 2);
lean_dec(v___x_419_);
lean_inc(v_declName_408_);
v___x_437_ = l_Lean_Environment_isProjectionFn(v_env_420_, v_declName_408_);
if (v___x_437_ == 0)
{
uint8_t v___x_438_; 
lean_inc(v_declName_408_);
lean_inc_ref(v_env_420_);
v___x_438_ = l_Lean_Environment_isConstructor(v_env_420_, v_declName_408_);
v___y_422_ = v___x_438_;
goto v___jp_421_;
}
else
{
v___y_422_ = v___x_437_;
goto v___jp_421_;
}
v___jp_413_:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_415_ = lean_unsigned_to_nat(1u);
v___x_416_ = lean_mk_empty_array_with_capacity(v___x_415_);
v___x_417_ = lean_array_push(v___x_416_, v_declName_408_);
v___x_418_ = l_Lean_compileDecls(v___x_417_, v___y_414_, v___y_410_, v___y_411_);
return v___x_418_;
}
v___jp_421_:
{
if (v___y_422_ == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec_ref(v_env_420_);
lean_dec(v_declName_408_);
v___x_423_ = lean_box(0);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
else
{
uint8_t v___x_425_; lean_object* v___x_426_; 
v___x_425_ = 0;
lean_inc(v_declName_408_);
v___x_426_ = l_Lean_Environment_find_x3f(v_env_420_, v_declName_408_, v___x_425_);
if (lean_obj_tag(v___x_426_) == 1)
{
lean_object* v_val_427_; 
v_val_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_val_427_);
lean_dec_ref_known(v___x_426_, 1);
if (lean_obj_tag(v_val_427_) == 2)
{
lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_435_; 
lean_dec(v_declName_408_);
v_isSharedCheck_435_ = !lean_is_exclusive(v_val_427_);
if (v_isSharedCheck_435_ == 0)
{
lean_object* v_unused_436_; 
v_unused_436_ = lean_ctor_get(v_val_427_, 0);
lean_dec(v_unused_436_);
v___x_429_ = v_val_427_;
v_isShared_430_ = v_isSharedCheck_435_;
goto v_resetjp_428_;
}
else
{
lean_dec(v_val_427_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_435_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_431_ = lean_box(0);
if (v_isShared_430_ == 0)
{
lean_ctor_set_tag(v___x_429_, 0);
lean_ctor_set(v___x_429_, 0, v___x_431_);
v___x_433_ = v___x_429_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
else
{
lean_dec(v_val_427_);
v___y_414_ = v___y_422_;
goto v___jp_413_;
}
}
else
{
lean_dec(v___x_426_);
v___y_414_ = v___y_422_;
goto v___jp_413_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_408_ = stack[0].m_obj;
lean_object* v_externAttrData_409_ = stack[1].m_obj;
lean_object* v___y_410_ = stack[2].m_obj;
lean_object* v___y_411_ = stack[3].m_obj;
lean_object* v_res_439_;
v_res_439_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v_declName_408_, v_externAttrData_409_, v___y_410_, v___y_411_);
stack->m_obj
 = v_res_439_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v_declName_440_, lean_object* v_externAttrData_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v_declName_440_, v_externAttrData_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v_externAttrData_441_);
return v_res_445_;
}
}
uint8_t l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(lean_object* v_env_446_, lean_object* v_n_447_, lean_object* v_x_448_){
_start:
{
uint8_t v___x_449_; uint8_t v___x_450_; 
v___x_449_ = 1;
v___x_450_ = l_Lean_Environment_contains(v_env_446_, v_n_447_, v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_env_446_ = stack[0].m_obj;
lean_object* v_n_447_ = stack[1].m_obj;
lean_object* v_x_448_ = stack[2].m_obj;
uint8_t v_res_451_;
v_res_451_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v_env_446_, v_n_447_, v_x_448_);
stack->m_num = v_res_451_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v_env_452_, lean_object* v_n_453_, lean_object* v_x_454_){
_start:
{
uint8_t v_res_455_; lean_object* v_r_456_; 
v_res_455_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v_env_452_, v_n_453_, v_x_454_);
lean_dec(v_x_454_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = ((lean_object*)(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_));
v___x_482_ = l_Lean_registerParametricAttribute___redArg(v___x_481_);
return v___x_482_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_483_;
v_res_483_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_();
stack->m_obj
 = v_res_483_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_();
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternAttrData_x3f(lean_object* v_env_486_, lean_object* v_n_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = lean_box(0);
v___x_489_ = l_Lean_externAttr;
v___x_490_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_488_, v___x_489_, v_env_486_, v_n_487_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(lean_object* v_pattern_491_, lean_object* v_it_492_, lean_object* v_r_493_){
_start:
{
lean_object* v_str_494_; lean_object* v_startInclusive_495_; lean_object* v_endExclusive_496_; lean_object* v___x_497_; uint8_t v_decide_498_; 
v_str_494_ = lean_ctor_get(v_pattern_491_, 0);
v_startInclusive_495_ = lean_ctor_get(v_pattern_491_, 1);
v_endExclusive_496_ = lean_ctor_get(v_pattern_491_, 2);
v___x_497_ = lean_nat_sub(v_endExclusive_496_, v_startInclusive_495_);
v_decide_498_ = lean_nat_dec_eq(v_it_492_, v___x_497_);
lean_dec(v___x_497_);
if (v_decide_498_ == 0)
{
lean_object* v___x_499_; uint32_t v_c_500_; uint32_t v___x_501_; uint8_t v___x_502_; 
v___x_499_ = lean_nat_add(v_startInclusive_495_, v_it_492_);
v_c_500_ = lean_string_utf8_get_fast(v_str_494_, v___x_499_);
v___x_501_ = 48;
v___x_502_ = lean_uint32_dec_le(v___x_501_, v_c_500_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
lean_dec(v___x_499_);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v_it_492_);
lean_ctor_set(v___x_503_, 1, v_r_493_);
return v___x_503_;
}
else
{
uint32_t v___x_504_; uint8_t v___x_505_; 
v___x_504_ = 57;
v___x_505_ = lean_uint32_dec_le(v_c_500_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; 
lean_dec(v___x_499_);
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v_it_492_);
lean_ctor_set(v___x_506_, 1, v_r_493_);
return v___x_506_;
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec(v_it_492_);
v___x_507_ = lean_string_utf8_next_fast(v_str_494_, v___x_499_);
lean_dec(v___x_499_);
v___x_508_ = lean_nat_sub(v___x_507_, v_startInclusive_495_);
v___x_509_ = lean_unsigned_to_nat(10u);
v___x_510_ = lean_nat_mul(v_r_493_, v___x_509_);
lean_dec(v_r_493_);
v___x_511_ = lean_uint32_to_nat(v_c_500_);
v___x_512_ = lean_unsigned_to_nat(48u);
v___x_513_ = lean_nat_sub(v___x_511_, v___x_512_);
lean_dec(v___x_511_);
v___x_514_ = lean_nat_add(v___x_510_, v___x_513_);
lean_dec(v___x_513_);
lean_dec(v___x_510_);
v_it_492_ = v___x_508_;
v_r_493_ = v___x_514_;
goto _start;
}
}
}
else
{
lean_object* v___x_516_; 
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v_it_492_);
lean_ctor_set(v___x_516_, 1, v_r_493_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum___boxed(lean_object* v_pattern_517_, lean_object* v_it_518_, lean_object* v_r_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(v_pattern_517_, v_it_518_, v_r_519_);
lean_dec_ref(v_pattern_517_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux(lean_object* v_args_522_, lean_object* v_pattern_523_, lean_object* v_it_524_, lean_object* v_r_525_){
_start:
{
lean_object* v___x_526_; uint8_t v_decide_527_; 
v___x_526_ = lean_string_utf8_byte_size(v_pattern_523_);
v_decide_527_ = lean_nat_dec_eq(v_it_524_, v___x_526_);
if (v_decide_527_ == 0)
{
uint32_t v_c_528_; uint32_t v___x_533_; uint8_t v___x_534_; 
v_c_528_ = lean_string_utf8_get_fast(v_pattern_523_, v_it_524_);
v___x_533_ = 35;
v___x_534_ = lean_uint32_dec_eq(v_c_528_, v___x_533_);
if (v___x_534_ == 0)
{
goto v___jp_529_;
}
else
{
if (v_decide_527_ == 0)
{
lean_object* v_it_u2081_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v_fst_539_; lean_object* v_snd_540_; lean_object* v___x_541_; lean_object* v_j_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v_it_u2081_535_ = lean_string_utf8_next_fast(v_pattern_523_, v_it_524_);
lean_dec(v_it_524_);
lean_inc_ref(v_pattern_523_);
v___x_536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_536_, 0, v_pattern_523_);
lean_ctor_set(v___x_536_, 1, v_it_u2081_535_);
lean_ctor_set(v___x_536_, 2, v___x_526_);
v___x_537_ = lean_unsigned_to_nat(0u);
v___x_538_ = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(v___x_536_, v___x_537_, v___x_537_);
lean_dec_ref_known(v___x_536_, 3);
v_fst_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_fst_539_);
v_snd_540_ = lean_ctor_get(v___x_538_, 1);
lean_inc(v_snd_540_);
lean_dec_ref(v___x_538_);
v___x_541_ = lean_unsigned_to_nat(1u);
v_j_542_ = lean_nat_sub(v_snd_540_, v___x_541_);
lean_dec(v_snd_540_);
v___x_543_ = lean_nat_add(v_it_u2081_535_, v_fst_539_);
lean_dec(v_fst_539_);
v___x_544_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_545_ = l_List_getD___redArg(v_args_522_, v_j_542_, v___x_544_);
v___x_546_ = lean_string_append(v_r_525_, v___x_545_);
lean_dec(v___x_545_);
v_it_524_ = v___x_543_;
v_r_525_ = v___x_546_;
goto _start;
}
else
{
goto v___jp_529_;
}
}
v___jp_529_:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_string_utf8_next_fast(v_pattern_523_, v_it_524_);
lean_dec(v_it_524_);
v___x_531_ = lean_string_push(v_r_525_, v_c_528_);
v_it_524_ = v___x_530_;
v_r_525_ = v___x_531_;
goto _start;
}
}
else
{
lean_dec(v_it_524_);
lean_dec_ref(v_pattern_523_);
return v_r_525_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux___boxed(lean_object* v_args_548_, lean_object* v_pattern_549_, lean_object* v_it_550_, lean_object* v_r_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_expandExternPatternAux(v_args_548_, v_pattern_549_, v_it_550_, v_r_551_);
lean_dec(v_args_548_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter___redArg(lean_object* v_x_553_, lean_object* v_h__1_554_){
_start:
{
lean_object* v_fst_555_; lean_object* v_snd_556_; lean_object* v___x_557_; 
v_fst_555_ = lean_ctor_get(v_x_553_, 0);
lean_inc(v_fst_555_);
v_snd_556_ = lean_ctor_get(v_x_553_, 1);
lean_inc(v_snd_556_);
lean_dec_ref(v_x_553_);
v___x_557_ = lean_apply_2(v_h__1_554_, v_fst_555_, v_snd_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter(lean_object* v_pattern_558_, lean_object* v_it_u2081_559_, lean_object* v_motive_560_, lean_object* v_x_561_, lean_object* v_h__1_562_){
_start:
{
lean_object* v_fst_563_; lean_object* v_snd_564_; lean_object* v___x_565_; 
v_fst_563_ = lean_ctor_get(v_x_561_, 0);
lean_inc(v_fst_563_);
v_snd_564_ = lean_ctor_get(v_x_561_, 1);
lean_inc(v_snd_564_);
lean_dec_ref(v_x_561_);
v___x_565_ = lean_apply_2(v_h__1_562_, v_fst_563_, v_snd_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter___boxed(lean_object* v_pattern_566_, lean_object* v_it_u2081_567_, lean_object* v_motive_568_, lean_object* v_x_569_, lean_object* v_h__1_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter(v_pattern_566_, v_it_u2081_567_, v_motive_568_, v_x_569_, v_h__1_570_);
lean_dec(v_it_u2081_567_);
lean_dec_ref(v_pattern_566_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPattern(lean_object* v_pattern_572_, lean_object* v_args_573_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_576_ = l_Lean_expandExternPatternAux(v_args_573_, v_pattern_572_, v___x_574_, v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPattern___boxed(lean_object* v_pattern_577_, lean_object* v_args_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_expandExternPattern(v_pattern_577_, v_args_578_);
lean_dec(v_args_578_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(lean_object* v_x_580_, lean_object* v_x_581_){
_start:
{
if (lean_obj_tag(v_x_581_) == 0)
{
return v_x_580_;
}
else
{
lean_object* v_head_582_; lean_object* v_tail_583_; lean_object* v___x_584_; 
v_head_582_ = lean_ctor_get(v_x_581_, 0);
v_tail_583_ = lean_ctor_get(v_x_581_, 1);
v___x_584_ = lean_string_append(v_x_580_, v_head_582_);
v_x_580_ = v___x_584_;
v_x_581_ = v_tail_583_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0___boxed(lean_object* v_x_586_, lean_object* v_x_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(v_x_586_, v_x_587_);
lean_dec(v_x_587_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleFnCall(lean_object* v_fn_592_, lean_object* v_args_593_){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_594_ = ((lean_object*)(l_Lean_mkSimpleFnCall___closed__0));
v___x_595_ = lean_string_append(v_fn_592_, v___x_594_);
v___x_596_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_597_ = ((lean_object*)(l_Lean_mkSimpleFnCall___closed__1));
v___x_598_ = l_List_intersperseTR___redArg(v___x_597_, v_args_593_);
v___x_599_ = l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(v___x_596_, v___x_598_);
lean_dec(v___x_598_);
v___x_600_ = lean_string_append(v___x_595_, v___x_599_);
lean_dec_ref(v___x_599_);
v___x_601_ = ((lean_object*)(l_Lean_mkSimpleFnCall___closed__2));
v___x_602_ = lean_string_append(v___x_600_, v___x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend(lean_object* v_x_603_){
_start:
{
if (lean_obj_tag(v_x_603_) == 3)
{
lean_object* v___x_604_; 
v___x_604_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
return v___x_604_;
}
else
{
lean_object* v_backend_605_; 
v_backend_605_ = lean_ctor_get(v_x_603_, 0);
lean_inc(v_backend_605_);
return v_backend_605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend___boxed(lean_object* v_x_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_ExternEntry_backend(v_x_606_);
lean_dec(v_x_606_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(lean_object* v_backend_608_, lean_object* v_x_609_){
_start:
{
if (lean_obj_tag(v_x_609_) == 0)
{
lean_object* v___x_610_; 
v___x_610_ = lean_box(0);
return v___x_610_;
}
else
{
lean_object* v_head_611_; lean_object* v_tail_612_; uint8_t v___y_614_; lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v_head_611_ = lean_ctor_get(v_x_609_, 0);
v_tail_612_ = lean_ctor_get(v_x_609_, 1);
v___x_617_ = l_Lean_ExternEntry_backend(v_head_611_);
v___x_618_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
v___x_619_ = lean_name_eq(v___x_617_, v___x_618_);
if (v___x_619_ == 0)
{
uint8_t v___x_620_; 
v___x_620_ = lean_name_eq(v___x_617_, v_backend_608_);
lean_dec(v___x_617_);
v___y_614_ = v___x_620_;
goto v___jp_613_;
}
else
{
lean_dec(v___x_617_);
v___y_614_ = v___x_619_;
goto v___jp_613_;
}
v___jp_613_:
{
if (v___y_614_ == 0)
{
v_x_609_ = v_tail_612_;
goto _start;
}
else
{
lean_object* v___x_616_; 
lean_inc(v_head_611_);
v___x_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_616_, 0, v_head_611_);
return v___x_616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0___boxed(lean_object* v_backend_621_, lean_object* v_x_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_621_, v_x_622_);
lean_dec(v_x_622_);
lean_dec(v_backend_621_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux(lean_object* v_backend_624_, lean_object* v_entries_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_624_, v_entries_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux___boxed(lean_object* v_backend_627_, lean_object* v_entries_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_getExternEntryForAux(v_backend_627_, v_entries_628_);
lean_dec(v_entries_628_);
lean_dec(v_backend_627_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor(lean_object* v_d_630_, lean_object* v_backend_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_631_, v_d_630_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor___boxed(lean_object* v_d_633_, lean_object* v_backend_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_getExternEntryFor(v_d_633_, v_backend_634_);
lean_dec(v_backend_634_);
lean_dec(v_d_633_);
return v_res_635_;
}
}
uint8_t l_Lean_isExtern(lean_object* v_env_636_, lean_object* v_fn_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_getExternAttrData_x3f(v_env_636_, v_fn_637_);
if (lean_obj_tag(v___x_638_) == 0)
{
uint8_t v___x_639_; 
v___x_639_ = 0;
return v___x_639_;
}
else
{
uint8_t v___x_640_; 
lean_dec_ref_known(v___x_638_, 1);
v___x_640_ = 1;
return v___x_640_;
}
}
}
LEAN_EXPORT void l_Lean_isExtern_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_636_ = stack[0].m_obj;
lean_object* v_fn_637_ = stack[1].m_obj;
uint8_t v_res_641_;
v_res_641_ = l_Lean_isExtern(v_env_636_, v_fn_637_);
stack->m_num = v_res_641_;
}
LEAN_EXPORT lean_object* l_Lean_isExtern___boxed(lean_object* v_env_642_, lean_object* v_fn_643_){
_start:
{
uint8_t v_res_644_; lean_object* v_r_645_; 
v_res_644_ = l_Lean_isExtern(v_env_642_, v_fn_643_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
uint8_t l_Lean_isExternC(lean_object* v_env_646_, lean_object* v_fn_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_getExternAttrData_x3f(v_env_646_, v_fn_647_);
if (lean_obj_tag(v___x_648_) == 1)
{
lean_object* v_val_649_; 
v_val_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_val_649_);
lean_dec_ref_known(v___x_648_, 1);
if (lean_obj_tag(v_val_649_) == 1)
{
lean_object* v_head_650_; 
v_head_650_ = lean_ctor_get(v_val_649_, 0);
if (lean_obj_tag(v_head_650_) == 2)
{
lean_object* v_backend_651_; 
v_backend_651_ = lean_ctor_get(v_head_650_, 0);
lean_inc(v_backend_651_);
if (lean_obj_tag(v_backend_651_) == 1)
{
lean_object* v_pre_652_; 
v_pre_652_ = lean_ctor_get(v_backend_651_, 0);
if (lean_obj_tag(v_pre_652_) == 0)
{
lean_object* v_tail_653_; lean_object* v_str_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v_tail_653_ = lean_ctor_get(v_val_649_, 1);
lean_inc(v_tail_653_);
lean_dec_ref_known(v_val_649_, 2);
v_str_654_ = lean_ctor_get(v_backend_651_, 1);
lean_inc_ref(v_str_654_);
lean_dec_ref_known(v_backend_651_, 2);
v___x_655_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__2));
v___x_656_ = lean_string_dec_eq(v_str_654_, v___x_655_);
lean_dec_ref(v_str_654_);
if (v___x_656_ == 0)
{
lean_dec(v_tail_653_);
return v___x_656_;
}
else
{
if (lean_obj_tag(v_tail_653_) == 0)
{
return v___x_656_;
}
else
{
uint8_t v___x_657_; 
lean_dec(v_tail_653_);
v___x_657_ = 0;
return v___x_657_;
}
}
}
else
{
uint8_t v___x_658_; 
lean_dec_ref_known(v_backend_651_, 2);
lean_dec_ref_known(v_val_649_, 2);
v___x_658_ = 0;
return v___x_658_;
}
}
else
{
uint8_t v___x_659_; 
lean_dec(v_backend_651_);
lean_dec_ref_known(v_val_649_, 2);
v___x_659_ = 0;
return v___x_659_;
}
}
else
{
uint8_t v___x_660_; 
lean_dec_ref_known(v_val_649_, 2);
v___x_660_ = 0;
return v___x_660_;
}
}
else
{
uint8_t v___x_661_; 
lean_dec(v_val_649_);
v___x_661_ = 0;
return v___x_661_;
}
}
else
{
uint8_t v___x_662_; 
lean_dec(v___x_648_);
v___x_662_ = 0;
return v___x_662_;
}
}
}
LEAN_EXPORT void l_Lean_isExternC_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_646_ = stack[0].m_obj;
lean_object* v_fn_647_ = stack[1].m_obj;
uint8_t v_res_663_;
v_res_663_ = l_Lean_isExternC(v_env_646_, v_fn_647_);
stack->m_num = v_res_663_;
}
LEAN_EXPORT lean_object* l_Lean_isExternC___boxed(lean_object* v_env_664_, lean_object* v_fn_665_){
_start:
{
uint8_t v_res_666_; lean_object* v_r_667_; 
v_res_666_ = l_Lean_isExternC(v_env_664_, v_fn_665_);
v_r_667_ = lean_box(v_res_666_);
return v_r_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternNameFor(lean_object* v_env_668_, lean_object* v_backend_669_, lean_object* v_fn_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_getExternAttrData_x3f(v_env_668_, v_fn_670_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v___x_672_; 
v___x_672_ = lean_box(0);
return v___x_672_;
}
else
{
lean_object* v_val_673_; lean_object* v___x_674_; 
v_val_673_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_val_673_);
lean_dec_ref_known(v___x_671_, 1);
v___x_674_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_669_, v_val_673_);
lean_dec(v_val_673_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v___x_675_; 
v___x_675_ = lean_box(0);
return v___x_675_;
}
else
{
lean_object* v_val_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_685_; 
v_val_676_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_685_ == 0)
{
v___x_678_ = v___x_674_;
v_isShared_679_ = v_isSharedCheck_685_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_val_676_);
lean_dec(v___x_674_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_685_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
if (lean_obj_tag(v_val_676_) == 2)
{
lean_object* v_fn_680_; lean_object* v___x_682_; 
v_fn_680_ = lean_ctor_get(v_val_676_, 1);
lean_inc_ref(v_fn_680_);
lean_dec_ref_known(v_val_676_, 2);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v_fn_680_);
v___x_682_ = v___x_678_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_fn_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
else
{
lean_object* v___x_684_; 
lean_del_object(v___x_678_);
lean_dec(v_val_676_);
v___x_684_ = lean_box(0);
return v___x_684_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExternNameFor___boxed(lean_object* v_env_686_, lean_object* v_backend_687_, lean_object* v_fn_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_getExternNameFor(v_env_686_, v_backend_687_, v_fn_688_);
lean_dec(v_backend_687_);
return v_res_689_;
}
}
lean_object* runtime_initialize_Lean_ProjFns(uint8_t builtin);
lean_object* runtime_initialize_Lean_Attributes(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_ExternAttr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_ProjFns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedExternAttrData_default = _init_l_Lean_instInhabitedExternAttrData_default();
lean_mark_persistent(l_Lean_instInhabitedExternAttrData_default);
l_Lean_instInhabitedExternAttrData = _init_l_Lean_instInhabitedExternAttrData();
lean_mark_persistent(l_Lean_instInhabitedExternAttrData);
res = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_externAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_externAttr);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_ExternAttr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_ProjFns(uint8_t builtin);
lean_object* initialize_Lean_Attributes(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_ExternAttr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ProjFns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ExternAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_ExternAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_ExternAttr(builtin);
}
#ifdef __cplusplus
}
#endif
