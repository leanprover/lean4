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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___redArg(lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_ctorIdx___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_instHashableExternEntry_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_instHashableExternEntry_hash___closed__0;
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
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "externAttr"};
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 152, 26, 79, 119, 188, 216, 230)}};
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "extern"};
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(146, 128, 231, 207, 24, 58, 115, 13)}};
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "builtin and foreign functions"};
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
LEAN_EXPORT lean_object* l_Lean_ExternEntry_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
default: 
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lean_ExternEntry_ctorIdx(v_x_6_);
lean_dec(v_x_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_ctorElim___redArg(lean_object* v_t_8_, lean_object* v_k_9_){
_start:
{
switch(lean_obj_tag(v_t_8_))
{
case 0:
{
lean_object* v_backend_10_; lean_object* v___x_11_; 
v_backend_10_ = lean_ctor_get(v_t_8_, 0);
lean_inc(v_backend_10_);
lean_dec_ref_known(v_t_8_, 1);
v___x_11_ = lean_apply_1(v_k_9_, v_backend_10_);
return v___x_11_;
}
case 3:
{
return v_k_9_;
}
default: 
{
lean_object* v_backend_12_; lean_object* v_pattern_13_; lean_object* v___x_14_; 
v_backend_12_ = lean_ctor_get(v_t_8_, 0);
lean_inc(v_backend_12_);
v_pattern_13_ = lean_ctor_get(v_t_8_, 1);
lean_inc_ref(v_pattern_13_);
lean_dec(v_t_8_);
v___x_14_ = lean_apply_2(v_k_9_, v_backend_12_, v_pattern_13_);
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_17_, v_k_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_ExternEntry_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_23_, v_h_24_, v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_adhoc_elim___redArg(lean_object* v_t_27_, lean_object* v_adhoc_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_27_, v_adhoc_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_adhoc_elim(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_adhoc_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_31_, v_adhoc_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_inline_elim___redArg(lean_object* v_t_35_, lean_object* v_inline_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_35_, v_inline_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_inline_elim(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_inline_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_39_, v_inline_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_standard_elim___redArg(lean_object* v_t_43_, lean_object* v_standard_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_43_, v_standard_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_standard_elim(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_standard_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_47_, v_standard_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_opaque_elim___redArg(lean_object* v_t_51_, lean_object* v_opaque_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_51_, v_opaque_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_opaque_elim(lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_opaque_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_55_, v_opaque_57_);
return v___x_58_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqExternEntry_beq(lean_object* v_x_59_, lean_object* v_x_60_){
_start:
{
lean_object* v_a_62_; lean_object* v_a_63_; lean_object* v_b_64_; lean_object* v_b_65_; 
switch(lean_obj_tag(v_x_59_))
{
case 0:
{
if (lean_obj_tag(v_x_60_) == 0)
{
lean_object* v_backend_68_; lean_object* v_backend_69_; uint8_t v___x_70_; 
v_backend_68_ = lean_ctor_get(v_x_59_, 0);
v_backend_69_ = lean_ctor_get(v_x_60_, 0);
v___x_70_ = lean_name_eq(v_backend_68_, v_backend_69_);
return v___x_70_;
}
else
{
uint8_t v___x_71_; 
v___x_71_ = 0;
return v___x_71_;
}
}
case 1:
{
if (lean_obj_tag(v_x_60_) == 1)
{
lean_object* v_backend_72_; lean_object* v_pattern_73_; lean_object* v_backend_74_; lean_object* v_pattern_75_; 
v_backend_72_ = lean_ctor_get(v_x_59_, 0);
v_pattern_73_ = lean_ctor_get(v_x_59_, 1);
v_backend_74_ = lean_ctor_get(v_x_60_, 0);
v_pattern_75_ = lean_ctor_get(v_x_60_, 1);
v_a_62_ = v_backend_72_;
v_a_63_ = v_pattern_73_;
v_b_64_ = v_backend_74_;
v_b_65_ = v_pattern_75_;
goto v___jp_61_;
}
else
{
uint8_t v___x_76_; 
v___x_76_ = 0;
return v___x_76_;
}
}
case 2:
{
if (lean_obj_tag(v_x_60_) == 2)
{
lean_object* v_backend_77_; lean_object* v_fn_78_; lean_object* v_backend_79_; lean_object* v_fn_80_; 
v_backend_77_ = lean_ctor_get(v_x_59_, 0);
v_fn_78_ = lean_ctor_get(v_x_59_, 1);
v_backend_79_ = lean_ctor_get(v_x_60_, 0);
v_fn_80_ = lean_ctor_get(v_x_60_, 1);
v_a_62_ = v_backend_77_;
v_a_63_ = v_fn_78_;
v_b_64_ = v_backend_79_;
v_b_65_ = v_fn_80_;
goto v___jp_61_;
}
else
{
uint8_t v___x_81_; 
v___x_81_ = 0;
return v___x_81_;
}
}
default: 
{
if (lean_obj_tag(v_x_60_) == 3)
{
uint8_t v___x_82_; 
v___x_82_ = 1;
return v___x_82_;
}
else
{
uint8_t v___x_83_; 
v___x_83_ = 0;
return v___x_83_;
}
}
}
v___jp_61_:
{
uint8_t v___x_66_; 
v___x_66_ = lean_name_eq(v_a_62_, v_b_64_);
if (v___x_66_ == 0)
{
return v___x_66_;
}
else
{
uint8_t v___x_67_; 
v___x_67_ = lean_string_dec_eq(v_a_63_, v_b_65_);
return v___x_67_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqExternEntry_beq___boxed(lean_object* v_x_84_, lean_object* v_x_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Lean_instBEqExternEntry_beq(v_x_84_, v_x_85_);
lean_dec(v_x_85_);
lean_dec(v_x_84_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
static uint64_t _init_l_Lean_instHashableExternEntry_hash___closed__0(void){
_start:
{
uint64_t v___x_90_; uint64_t v___x_91_; uint64_t v___x_92_; 
v___x_90_ = 1723ULL;
v___x_91_ = 0ULL;
v___x_92_ = lean_uint64_mix_hash(v___x_91_, v___x_90_);
return v___x_92_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableExternEntry_hash(lean_object* v_x_93_){
_start:
{
switch(lean_obj_tag(v_x_93_))
{
case 0:
{
lean_object* v_backend_94_; uint64_t v___x_95_; 
v_backend_94_ = lean_ctor_get(v_x_93_, 0);
v___x_95_ = 0ULL;
if (lean_obj_tag(v_backend_94_) == 0)
{
uint64_t v___x_96_; 
v___x_96_ = lean_uint64_once(&l_Lean_instHashableExternEntry_hash___closed__0, &l_Lean_instHashableExternEntry_hash___closed__0_once, _init_l_Lean_instHashableExternEntry_hash___closed__0);
return v___x_96_;
}
else
{
uint64_t v_hash_97_; uint64_t v___x_98_; 
v_hash_97_ = lean_ctor_get_uint64(v_backend_94_, sizeof(void*)*2);
v___x_98_ = lean_uint64_mix_hash(v___x_95_, v_hash_97_);
return v___x_98_;
}
}
case 1:
{
lean_object* v_backend_99_; lean_object* v_pattern_100_; uint64_t v___x_101_; uint64_t v___y_103_; 
v_backend_99_ = lean_ctor_get(v_x_93_, 0);
v_pattern_100_ = lean_ctor_get(v_x_93_, 1);
v___x_101_ = 1ULL;
if (lean_obj_tag(v_backend_99_) == 0)
{
uint64_t v___x_107_; 
v___x_107_ = 1723ULL;
v___y_103_ = v___x_107_;
goto v___jp_102_;
}
else
{
uint64_t v_hash_108_; 
v_hash_108_ = lean_ctor_get_uint64(v_backend_99_, sizeof(void*)*2);
v___y_103_ = v_hash_108_;
goto v___jp_102_;
}
v___jp_102_:
{
uint64_t v___x_104_; uint64_t v___x_105_; uint64_t v___x_106_; 
v___x_104_ = lean_uint64_mix_hash(v___x_101_, v___y_103_);
v___x_105_ = lean_string_hash(v_pattern_100_);
v___x_106_ = lean_uint64_mix_hash(v___x_104_, v___x_105_);
return v___x_106_;
}
}
case 2:
{
lean_object* v_backend_109_; lean_object* v_fn_110_; uint64_t v___x_111_; uint64_t v___y_113_; 
v_backend_109_ = lean_ctor_get(v_x_93_, 0);
v_fn_110_ = lean_ctor_get(v_x_93_, 1);
v___x_111_ = 2ULL;
if (lean_obj_tag(v_backend_109_) == 0)
{
uint64_t v___x_117_; 
v___x_117_ = 1723ULL;
v___y_113_ = v___x_117_;
goto v___jp_112_;
}
else
{
uint64_t v_hash_118_; 
v_hash_118_ = lean_ctor_get_uint64(v_backend_109_, sizeof(void*)*2);
v___y_113_ = v_hash_118_;
goto v___jp_112_;
}
v___jp_112_:
{
uint64_t v___x_114_; uint64_t v___x_115_; uint64_t v___x_116_; 
v___x_114_ = lean_uint64_mix_hash(v___x_111_, v___y_113_);
v___x_115_ = lean_string_hash(v_fn_110_);
v___x_116_ = lean_uint64_mix_hash(v___x_114_, v___x_115_);
return v___x_116_;
}
}
default: 
{
uint64_t v___x_119_; 
v___x_119_ = 3ULL;
return v___x_119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableExternEntry_hash___boxed(lean_object* v_x_120_){
_start:
{
uint64_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l_Lean_instHashableExternEntry_hash(v_x_120_);
lean_dec(v_x_120_);
v_r_122_ = lean_box_uint64(v_res_121_);
return v_r_122_;
}
}
static lean_object* _init_l_Lean_instInhabitedExternAttrData_default(void){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lean_box(0);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_instInhabitedExternAttrData(void){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lean_box(0);
return v___x_126_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0(lean_object* v_x_127_, lean_object* v_x_128_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
if (lean_obj_tag(v_x_128_) == 0)
{
uint8_t v___x_129_; 
v___x_129_ = 1;
return v___x_129_;
}
else
{
uint8_t v___x_130_; 
v___x_130_ = 0;
return v___x_130_;
}
}
else
{
if (lean_obj_tag(v_x_128_) == 0)
{
uint8_t v___x_131_; 
v___x_131_ = 0;
return v___x_131_;
}
else
{
lean_object* v_head_132_; lean_object* v_tail_133_; lean_object* v_head_134_; lean_object* v_tail_135_; uint8_t v___x_136_; 
v_head_132_ = lean_ctor_get(v_x_127_, 0);
v_tail_133_ = lean_ctor_get(v_x_127_, 1);
v_head_134_ = lean_ctor_get(v_x_128_, 0);
v_tail_135_ = lean_ctor_get(v_x_128_, 1);
v___x_136_ = l_Lean_instBEqExternEntry_beq(v_head_132_, v_head_134_);
if (v___x_136_ == 0)
{
return v___x_136_;
}
else
{
v_x_127_ = v_tail_133_;
v_x_128_ = v_tail_135_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0___boxed(lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0(v_x_138_, v_x_139_);
lean_dec(v_x_139_);
lean_dec(v_x_138_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqExternAttrData_beq(lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
uint8_t v___x_144_; 
v___x_144_ = l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0(v_x_142_, v_x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqExternAttrData_beq___boxed(lean_object* v_x_145_, lean_object* v_x_146_){
_start:
{
uint8_t v_res_147_; lean_object* v_r_148_; 
v_res_147_ = l_Lean_instBEqExternAttrData_beq(v_x_145_, v_x_146_);
lean_dec(v_x_146_);
lean_dec(v_x_145_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0(uint64_t v_x_151_, lean_object* v_x_152_){
_start:
{
if (lean_obj_tag(v_x_152_) == 0)
{
return v_x_151_;
}
else
{
lean_object* v_head_153_; lean_object* v_tail_154_; uint64_t v___x_155_; uint64_t v___x_156_; 
v_head_153_ = lean_ctor_get(v_x_152_, 0);
v_tail_154_ = lean_ctor_get(v_x_152_, 1);
v___x_155_ = l_Lean_instHashableExternEntry_hash(v_head_153_);
v___x_156_ = lean_uint64_mix_hash(v_x_151_, v___x_155_);
v_x_151_ = v___x_156_;
v_x_152_ = v_tail_154_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0___boxed(lean_object* v_x_158_, lean_object* v_x_159_){
_start:
{
uint64_t v_x_57__boxed_160_; uint64_t v_res_161_; lean_object* v_r_162_; 
v_x_57__boxed_160_ = lean_unbox_uint64(v_x_158_);
lean_dec_ref(v_x_158_);
v_res_161_ = l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0(v_x_57__boxed_160_, v_x_159_);
lean_dec(v_x_159_);
v_r_162_ = lean_box_uint64(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableExternAttrData_hash(lean_object* v_x_163_){
_start:
{
uint64_t v___x_164_; uint64_t v___x_165_; uint64_t v___x_166_; uint64_t v___x_167_; 
v___x_164_ = 0ULL;
v___x_165_ = 7ULL;
v___x_166_ = l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0(v___x_165_, v_x_163_);
v___x_167_ = lean_uint64_mix_hash(v___x_164_, v___x_166_);
return v___x_167_;
}
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
v___x_173_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1);
v___x_177_ = lean_unsigned_to_nat(0u);
v___x_178_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
lean_ctor_set(v___x_178_, 2, v___x_177_);
lean_ctor_set(v___x_178_, 3, v___x_177_);
lean_ctor_set(v___x_178_, 4, v___x_176_);
lean_ctor_set(v___x_178_, 5, v___x_176_);
lean_ctor_set(v___x_178_, 6, v___x_176_);
lean_ctor_set(v___x_178_, 7, v___x_176_);
lean_ctor_set(v___x_178_, 8, v___x_176_);
lean_ctor_set(v___x_178_, 9, v___x_176_);
lean_ctor_set(v___x_178_, 10, v___x_176_);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = lean_unsigned_to_nat(32u);
v___x_180_ = lean_mk_empty_array_with_capacity(v___x_179_);
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_182_ = ((size_t)5ULL);
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = lean_unsigned_to_nat(32u);
v___x_185_ = lean_mk_empty_array_with_capacity(v___x_184_);
v___x_186_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3);
v___x_187_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v___x_185_);
lean_ctor_set(v___x_187_, 2, v___x_183_);
lean_ctor_set(v___x_187_, 3, v___x_183_);
lean_ctor_set_usize(v___x_187_, 4, v___x_182_);
return v___x_187_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_188_ = lean_box(1);
v___x_189_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4);
v___x_190_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1);
v___x_191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v___x_189_);
lean_ctor_set(v___x_191_, 2, v___x_188_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1(lean_object* v_msgData_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v___x_196_; lean_object* v_env_197_; lean_object* v_options_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_196_ = lean_st_ref_get(v___y_194_);
v_env_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc_ref(v_env_197_);
lean_dec(v___x_196_);
v_options_198_ = lean_ctor_get(v___y_193_, 1);
v___x_199_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2);
v___x_200_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_198_);
v___x_201_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_201_, 0, v_env_197_);
lean_ctor_set(v___x_201_, 1, v___x_199_);
lean_ctor_set(v___x_201_, 2, v___x_200_);
lean_ctor_set(v___x_201_, 3, v_options_198_);
v___x_202_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v_msgData_192_);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1(v_msgData_204_, v___y_205_, v___y_206_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(lean_object* v_msg_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_ref_213_; lean_object* v___x_214_; lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_223_; 
v_ref_213_ = lean_ctor_get(v___y_210_, 4);
v___x_214_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1(v_msg_209_, v___y_210_, v___y_211_);
v_a_215_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_223_ == 0)
{
v___x_217_ = v___x_214_;
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_214_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_221_; 
lean_inc(v_ref_213_);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v_ref_213_);
lean_ctor_set(v___x_219_, 1, v_a_215_);
if (v_isShared_218_ == 0)
{
lean_ctor_set_tag(v___x_217_, 1);
lean_ctor_set(v___x_217_, 0, v___x_219_);
v___x_221_ = v___x_217_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg___boxed(lean_object* v_msg_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_224_, v___y_225_, v___y_226_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(lean_object* v_ref_229_, lean_object* v_msg_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_toCold_234_; lean_object* v_options_235_; lean_object* v_currRecDepth_236_; lean_object* v_maxRecDepth_237_; lean_object* v_ref_238_; lean_object* v_currNamespace_239_; lean_object* v_openDecls_240_; lean_object* v_initHeartbeats_241_; lean_object* v_maxHeartbeats_242_; lean_object* v_currMacroScope_243_; uint8_t v_diag_244_; uint8_t v_suppressElabErrors_245_; lean_object* v_ref_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_toCold_234_ = lean_ctor_get(v___y_231_, 0);
v_options_235_ = lean_ctor_get(v___y_231_, 1);
v_currRecDepth_236_ = lean_ctor_get(v___y_231_, 2);
v_maxRecDepth_237_ = lean_ctor_get(v___y_231_, 3);
v_ref_238_ = lean_ctor_get(v___y_231_, 4);
v_currNamespace_239_ = lean_ctor_get(v___y_231_, 5);
v_openDecls_240_ = lean_ctor_get(v___y_231_, 6);
v_initHeartbeats_241_ = lean_ctor_get(v___y_231_, 7);
v_maxHeartbeats_242_ = lean_ctor_get(v___y_231_, 8);
v_currMacroScope_243_ = lean_ctor_get(v___y_231_, 9);
v_diag_244_ = lean_ctor_get_uint8(v___y_231_, sizeof(void*)*10);
v_suppressElabErrors_245_ = lean_ctor_get_uint8(v___y_231_, sizeof(void*)*10 + 1);
v_ref_246_ = l_Lean_replaceRef(v_ref_229_, v_ref_238_);
lean_inc(v_currMacroScope_243_);
lean_inc(v_maxHeartbeats_242_);
lean_inc(v_initHeartbeats_241_);
lean_inc(v_openDecls_240_);
lean_inc(v_currNamespace_239_);
lean_inc(v_maxRecDepth_237_);
lean_inc(v_currRecDepth_236_);
lean_inc_ref(v_options_235_);
lean_inc_ref(v_toCold_234_);
v___x_247_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_247_, 0, v_toCold_234_);
lean_ctor_set(v___x_247_, 1, v_options_235_);
lean_ctor_set(v___x_247_, 2, v_currRecDepth_236_);
lean_ctor_set(v___x_247_, 3, v_maxRecDepth_237_);
lean_ctor_set(v___x_247_, 4, v_ref_246_);
lean_ctor_set(v___x_247_, 5, v_currNamespace_239_);
lean_ctor_set(v___x_247_, 6, v_openDecls_240_);
lean_ctor_set(v___x_247_, 7, v_initHeartbeats_241_);
lean_ctor_set(v___x_247_, 8, v_maxHeartbeats_242_);
lean_ctor_set(v___x_247_, 9, v_currMacroScope_243_);
lean_ctor_set_uint8(v___x_247_, sizeof(void*)*10, v_diag_244_);
lean_ctor_set_uint8(v___x_247_, sizeof(void*)*10 + 1, v_suppressElabErrors_245_);
v___x_248_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_230_, v___x_247_, v___y_232_);
lean_dec_ref_known(v___x_247_, 10);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg___boxed(lean_object* v_ref_249_, lean_object* v_msg_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v_ref_249_, v_msg_250_, v___y_251_, v___y_252_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec(v_ref_249_);
return v_res_254_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__0));
v___x_257_ = l_Lean_stringToMessageData(v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(lean_object* v_as_261_, size_t v_sz_262_, size_t v_i_263_, lean_object* v_b_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_a_269_; uint8_t v___x_273_; 
v___x_273_ = lean_usize_dec_lt(v_i_263_, v_sz_262_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; 
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v_b_264_);
return v___x_274_;
}
else
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v_a_277_; lean_object* v___y_279_; lean_object* v_str_280_; lean_object* v___y_288_; lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_275_ = lean_unsigned_to_nat(1u);
v___x_276_ = lean_unsigned_to_nat(0u);
v_a_277_ = lean_array_uget_borrowed(v_as_261_, v_i_263_);
v___x_304_ = l_Lean_Syntax_getArg(v_a_277_, v___x_276_);
v___x_305_ = l_Lean_Syntax_isNone(v___x_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = l_Lean_Syntax_getArg(v___x_304_, v___x_276_);
lean_dec(v___x_304_);
v___x_307_ = l_Lean_Syntax_getId(v___x_306_);
lean_dec(v___x_306_);
v___y_288_ = v___x_307_;
goto v___jp_287_;
}
else
{
lean_object* v___x_308_; 
lean_dec(v___x_304_);
v___x_308_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
v___y_288_ = v___x_308_;
goto v___jp_287_;
}
v___jp_278_:
{
lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_281_ = l_Lean_Syntax_getArg(v_a_277_, v___x_275_);
v___x_282_ = l_Lean_Syntax_isNone(v___x_281_);
lean_dec(v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_283_, 0, v___y_279_);
lean_ctor_set(v___x_283_, 1, v_str_280_);
v___x_284_ = lean_array_push(v_b_264_, v___x_283_);
v_a_269_ = v___x_284_;
goto v___jp_268_;
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_285_, 0, v___y_279_);
lean_ctor_set(v___x_285_, 1, v_str_280_);
v___x_286_ = lean_array_push(v_b_264_, v___x_285_);
v_a_269_ = v___x_286_;
goto v___jp_268_;
}
}
v___jp_287_:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = lean_unsigned_to_nat(2u);
v___x_290_ = l_Lean_Syntax_getArg(v_a_277_, v___x_289_);
v___x_291_ = l_Lean_Syntax_isStrLit_x3f(v___x_290_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1);
v___x_293_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v___x_290_, v___x_292_, v___y_265_, v___y_266_);
lean_dec(v___x_290_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_294_);
lean_dec_ref_known(v___x_293_, 1);
v___y_279_ = v___y_288_;
v_str_280_ = v_a_294_;
goto v___jp_278_;
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
lean_dec(v___y_288_);
lean_dec_ref(v_b_264_);
v_a_295_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___x_293_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_293_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
else
{
lean_object* v_val_303_; 
lean_dec(v___x_290_);
v_val_303_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_val_303_);
lean_dec_ref_known(v___x_291_, 1);
v___y_279_ = v___y_288_;
v_str_280_ = v_val_303_;
goto v___jp_278_;
}
}
}
v___jp_268_:
{
size_t v___x_270_; size_t v___x_271_; 
v___x_270_ = ((size_t)1ULL);
v___x_271_ = lean_usize_add(v_i_263_, v___x_270_);
v_i_263_ = v___x_271_;
v_b_264_ = v_a_269_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___boxed(lean_object* v_as_309_, lean_object* v_sz_310_, lean_object* v_i_311_, lean_object* v_b_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
size_t v_sz_boxed_316_; size_t v_i_boxed_317_; lean_object* v_res_318_; 
v_sz_boxed_316_ = lean_unbox_usize(v_sz_310_);
lean_dec(v_sz_310_);
v_i_boxed_317_ = lean_unbox_usize(v_i_311_);
lean_dec(v_i_311_);
v_res_318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(v_as_309_, v_sz_boxed_316_, v_i_boxed_317_, v_b_312_, v___y_313_, v___y_314_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec_ref(v_as_309_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(lean_object* v_stx_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v_entriesStx_332_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = l_Lean_Syntax_getArg(v_stx_326_, v___x_330_);
v_entriesStx_332_ = l_Lean_Syntax_getArgs(v___x_331_);
lean_dec(v___x_331_);
v___x_333_ = lean_array_get_size(v_entriesStx_332_);
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_335_ = lean_nat_dec_eq(v___x_333_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v_entries_336_; size_t v_sz_337_; size_t v___x_338_; lean_object* v___x_339_; 
v_entries_336_ = ((lean_object*)(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__0));
v_sz_337_ = lean_array_size(v_entriesStx_332_);
v___x_338_ = ((size_t)0ULL);
v___x_339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(v_entriesStx_332_, v_sz_337_, v___x_338_, v_entries_336_, v_a_327_, v_a_328_);
lean_dec_ref(v_entriesStx_332_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_348_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_348_ == 0)
{
v___x_342_ = v___x_339_;
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_344_ = lean_array_to_list(v_a_340_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v___x_344_);
v___x_346_ = v___x_342_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
v_a_349_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_339_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_339_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec_ref(v_entriesStx_332_);
v___x_357_ = ((lean_object*)(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2));
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___boxed(lean_object* v_stx_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(v_stx_359_, v_a_360_, v_a_361_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec(v_stx_359_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(lean_object* v_00_u03b1_364_, lean_object* v_ref_365_, lean_object* v_msg_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v_ref_365_, v_msg_366_, v___y_367_, v___y_368_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___boxed(lean_object* v_00_u03b1_371_, lean_object* v_ref_372_, lean_object* v_msg_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(v_00_u03b1_371_, v_ref_372_, v_msg_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v_ref_372_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0(lean_object* v_00_u03b1_378_, lean_object* v_msg_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_379_, v___y_380_, v___y_381_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___boxed(lean_object* v_00_u03b1_384_, lean_object* v_msg_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0(v_00_u03b1_384_, v_msg_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(lean_object* v_x_390_, lean_object* v_stx_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(v_stx_391_, v___y_392_, v___y_393_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v_x_396_, lean_object* v_stx_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v_x_396_, v_stx_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v_stx_397_);
lean_dec(v_x_396_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(lean_object* v_declName_402_, lean_object* v_externAttrData_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
uint8_t v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___x_415_; lean_object* v_env_416_; uint8_t v___y_418_; uint8_t v___x_433_; 
v___x_415_ = lean_st_ref_get(v___y_405_);
v_env_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc_ref_n(v_env_416_, 2);
lean_dec(v___x_415_);
lean_inc(v_declName_402_);
v___x_433_ = l_Lean_Environment_isProjectionFn(v_env_416_, v_declName_402_);
if (v___x_433_ == 0)
{
uint8_t v___x_434_; 
lean_inc(v_declName_402_);
lean_inc_ref(v_env_416_);
v___x_434_ = l_Lean_Environment_isConstructor(v_env_416_, v_declName_402_);
v___y_418_ = v___x_434_;
goto v___jp_417_;
}
else
{
v___y_418_ = v___x_433_;
goto v___jp_417_;
}
v___jp_407_:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = lean_mk_empty_array_with_capacity(v___x_411_);
v___x_413_ = lean_array_push(v___x_412_, v_declName_402_);
v___x_414_ = l_Lean_compileDecls(v___x_413_, v___y_408_, v___y_409_, v___y_410_);
return v___x_414_;
}
v___jp_417_:
{
if (v___y_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec_ref(v_env_416_);
lean_dec(v_declName_402_);
v___x_419_ = lean_box(0);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
else
{
uint8_t v___x_421_; lean_object* v___x_422_; 
v___x_421_ = 0;
lean_inc(v_declName_402_);
v___x_422_ = l_Lean_Environment_find_x3f(v_env_416_, v_declName_402_, v___x_421_);
if (lean_obj_tag(v___x_422_) == 1)
{
lean_object* v_val_423_; 
v_val_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_val_423_);
lean_dec_ref_known(v___x_422_, 1);
if (lean_obj_tag(v_val_423_) == 2)
{
lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_431_; 
lean_dec(v_declName_402_);
v_isSharedCheck_431_ = !lean_is_exclusive(v_val_423_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; 
v_unused_432_ = lean_ctor_get(v_val_423_, 0);
lean_dec(v_unused_432_);
v___x_425_ = v_val_423_;
v_isShared_426_ = v_isSharedCheck_431_;
goto v_resetjp_424_;
}
else
{
lean_dec(v_val_423_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_431_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_427_ = lean_box(0);
if (v_isShared_426_ == 0)
{
lean_ctor_set_tag(v___x_425_, 0);
lean_ctor_set(v___x_425_, 0, v___x_427_);
v___x_429_ = v___x_425_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
else
{
lean_dec(v_val_423_);
v___y_408_ = v___y_418_;
v___y_409_ = v___y_404_;
v___y_410_ = v___y_405_;
goto v___jp_407_;
}
}
else
{
lean_dec(v___x_422_);
v___y_408_ = v___y_418_;
v___y_409_ = v___y_404_;
v___y_410_ = v___y_405_;
goto v___jp_407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v_declName_435_, lean_object* v_externAttrData_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v_declName_435_, v_externAttrData_436_, v___y_437_, v___y_438_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v_externAttrData_436_);
return v_res_440_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(uint8_t v___x_441_, lean_object* v_env_442_, lean_object* v_n_443_, lean_object* v_x_444_){
_start:
{
uint8_t v___x_445_; 
v___x_445_ = l_Lean_Environment_contains(v_env_442_, v_n_443_, v___x_441_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v___x_446_, lean_object* v_env_447_, lean_object* v_n_448_, lean_object* v_x_449_){
_start:
{
uint8_t v___x_560__boxed_450_; uint8_t v_res_451_; lean_object* v_r_452_; 
v___x_560__boxed_450_ = lean_unbox(v___x_446_);
v_res_451_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v___x_560__boxed_450_, v_env_447_, v_n_448_, v_x_449_);
lean_dec(v_x_449_);
v_r_452_ = lean_box(v_res_451_);
return v_r_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = ((lean_object*)(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_));
v___x_480_ = l_Lean_registerParametricAttribute___redArg(v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_();
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternAttrData_x3f(lean_object* v_env_483_, lean_object* v_n_484_){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_485_ = lean_box(0);
v___x_486_ = l_Lean_externAttr;
v___x_487_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_485_, v___x_486_, v_env_483_, v_n_484_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(lean_object* v_pattern_488_, lean_object* v_it_489_, lean_object* v_r_490_){
_start:
{
lean_object* v_str_491_; lean_object* v_startInclusive_492_; lean_object* v_endExclusive_493_; lean_object* v___x_494_; uint8_t v_decide_495_; 
v_str_491_ = lean_ctor_get(v_pattern_488_, 0);
v_startInclusive_492_ = lean_ctor_get(v_pattern_488_, 1);
v_endExclusive_493_ = lean_ctor_get(v_pattern_488_, 2);
v___x_494_ = lean_nat_sub(v_endExclusive_493_, v_startInclusive_492_);
v_decide_495_ = lean_nat_dec_eq(v_it_489_, v___x_494_);
lean_dec(v___x_494_);
if (v_decide_495_ == 0)
{
lean_object* v___x_496_; uint32_t v_c_497_; uint32_t v___x_498_; uint8_t v___x_499_; 
v___x_496_ = lean_nat_add(v_startInclusive_492_, v_it_489_);
v_c_497_ = lean_string_utf8_get_fast(v_str_491_, v___x_496_);
v___x_498_ = 48;
v___x_499_ = lean_uint32_dec_le(v___x_498_, v_c_497_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; 
lean_dec(v___x_496_);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v_it_489_);
lean_ctor_set(v___x_500_, 1, v_r_490_);
return v___x_500_;
}
else
{
uint32_t v___x_501_; uint8_t v___x_502_; 
v___x_501_ = 57;
v___x_502_ = lean_uint32_dec_le(v_c_497_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
lean_dec(v___x_496_);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v_it_489_);
lean_ctor_set(v___x_503_, 1, v_r_490_);
return v___x_503_;
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec(v_it_489_);
v___x_504_ = lean_string_utf8_next_fast(v_str_491_, v___x_496_);
lean_dec(v___x_496_);
v___x_505_ = lean_nat_sub(v___x_504_, v_startInclusive_492_);
v___x_506_ = lean_unsigned_to_nat(10u);
v___x_507_ = lean_nat_mul(v_r_490_, v___x_506_);
lean_dec(v_r_490_);
v___x_508_ = lean_uint32_to_nat(v_c_497_);
v___x_509_ = lean_unsigned_to_nat(48u);
v___x_510_ = lean_nat_sub(v___x_508_, v___x_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_nat_add(v___x_507_, v___x_510_);
lean_dec(v___x_510_);
lean_dec(v___x_507_);
v_it_489_ = v___x_505_;
v_r_490_ = v___x_511_;
goto _start;
}
}
}
else
{
lean_object* v___x_513_; 
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v_it_489_);
lean_ctor_set(v___x_513_, 1, v_r_490_);
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum___boxed(lean_object* v_pattern_514_, lean_object* v_it_515_, lean_object* v_r_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(v_pattern_514_, v_it_515_, v_r_516_);
lean_dec_ref(v_pattern_514_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux(lean_object* v_args_519_, lean_object* v_pattern_520_, lean_object* v_it_521_, lean_object* v_r_522_){
_start:
{
lean_object* v___x_523_; uint8_t v_decide_524_; 
v___x_523_ = lean_string_utf8_byte_size(v_pattern_520_);
v_decide_524_ = lean_nat_dec_eq(v_it_521_, v___x_523_);
if (v_decide_524_ == 0)
{
uint32_t v_c_525_; uint32_t v___x_530_; uint8_t v___x_531_; 
v_c_525_ = lean_string_utf8_get_fast(v_pattern_520_, v_it_521_);
v___x_530_ = 35;
v___x_531_ = lean_uint32_dec_eq(v_c_525_, v___x_530_);
if (v___x_531_ == 0)
{
goto v___jp_526_;
}
else
{
if (v_decide_524_ == 0)
{
lean_object* v_it_u2081_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v_fst_536_; lean_object* v_snd_537_; lean_object* v___x_538_; lean_object* v_j_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v_it_u2081_532_ = lean_string_utf8_next_fast(v_pattern_520_, v_it_521_);
lean_dec(v_it_521_);
lean_inc_ref(v_pattern_520_);
v___x_533_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_533_, 0, v_pattern_520_);
lean_ctor_set(v___x_533_, 1, v_it_u2081_532_);
lean_ctor_set(v___x_533_, 2, v___x_523_);
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_535_ = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(v___x_533_, v___x_534_, v___x_534_);
lean_dec_ref_known(v___x_533_, 3);
v_fst_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_fst_536_);
v_snd_537_ = lean_ctor_get(v___x_535_, 1);
lean_inc(v_snd_537_);
lean_dec_ref(v___x_535_);
v___x_538_ = lean_unsigned_to_nat(1u);
v_j_539_ = lean_nat_sub(v_snd_537_, v___x_538_);
lean_dec(v_snd_537_);
v___x_540_ = lean_nat_add(v_it_u2081_532_, v_fst_536_);
lean_dec(v_fst_536_);
v___x_541_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_542_ = l_List_getD___redArg(v_args_519_, v_j_539_, v___x_541_);
v___x_543_ = lean_string_append(v_r_522_, v___x_542_);
lean_dec(v___x_542_);
v_it_521_ = v___x_540_;
v_r_522_ = v___x_543_;
goto _start;
}
else
{
goto v___jp_526_;
}
}
v___jp_526_:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_string_utf8_next_fast(v_pattern_520_, v_it_521_);
lean_dec(v_it_521_);
v___x_528_ = lean_string_push(v_r_522_, v_c_525_);
v_it_521_ = v___x_527_;
v_r_522_ = v___x_528_;
goto _start;
}
}
else
{
lean_dec(v_it_521_);
lean_dec_ref(v_pattern_520_);
return v_r_522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux___boxed(lean_object* v_args_545_, lean_object* v_pattern_546_, lean_object* v_it_547_, lean_object* v_r_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_expandExternPatternAux(v_args_545_, v_pattern_546_, v_it_547_, v_r_548_);
lean_dec(v_args_545_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter___redArg(lean_object* v_x_550_, lean_object* v_h__1_551_){
_start:
{
lean_object* v_fst_552_; lean_object* v_snd_553_; lean_object* v___x_554_; 
v_fst_552_ = lean_ctor_get(v_x_550_, 0);
lean_inc(v_fst_552_);
v_snd_553_ = lean_ctor_get(v_x_550_, 1);
lean_inc(v_snd_553_);
lean_dec_ref(v_x_550_);
v___x_554_ = lean_apply_2(v_h__1_551_, v_fst_552_, v_snd_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter(lean_object* v_pattern_555_, lean_object* v_it_u2081_556_, lean_object* v_motive_557_, lean_object* v_x_558_, lean_object* v_h__1_559_){
_start:
{
lean_object* v_fst_560_; lean_object* v_snd_561_; lean_object* v___x_562_; 
v_fst_560_ = lean_ctor_get(v_x_558_, 0);
lean_inc(v_fst_560_);
v_snd_561_ = lean_ctor_get(v_x_558_, 1);
lean_inc(v_snd_561_);
lean_dec_ref(v_x_558_);
v___x_562_ = lean_apply_2(v_h__1_559_, v_fst_560_, v_snd_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter___boxed(lean_object* v_pattern_563_, lean_object* v_it_u2081_564_, lean_object* v_motive_565_, lean_object* v_x_566_, lean_object* v_h__1_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter(v_pattern_563_, v_it_u2081_564_, v_motive_565_, v_x_566_, v_h__1_567_);
lean_dec(v_it_u2081_564_);
lean_dec_ref(v_pattern_563_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPattern(lean_object* v_pattern_569_, lean_object* v_args_570_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_573_ = l_Lean_expandExternPatternAux(v_args_570_, v_pattern_569_, v___x_571_, v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPattern___boxed(lean_object* v_pattern_574_, lean_object* v_args_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_expandExternPattern(v_pattern_574_, v_args_575_);
lean_dec(v_args_575_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(lean_object* v_x_577_, lean_object* v_x_578_){
_start:
{
if (lean_obj_tag(v_x_578_) == 0)
{
return v_x_577_;
}
else
{
lean_object* v_head_579_; lean_object* v_tail_580_; lean_object* v___x_581_; 
v_head_579_ = lean_ctor_get(v_x_578_, 0);
v_tail_580_ = lean_ctor_get(v_x_578_, 1);
v___x_581_ = lean_string_append(v_x_577_, v_head_579_);
v_x_577_ = v___x_581_;
v_x_578_ = v_tail_580_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0___boxed(lean_object* v_x_583_, lean_object* v_x_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(v_x_583_, v_x_584_);
lean_dec(v_x_584_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleFnCall(lean_object* v_fn_589_, lean_object* v_args_590_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_591_ = ((lean_object*)(l_Lean_mkSimpleFnCall___closed__0));
v___x_592_ = lean_string_append(v_fn_589_, v___x_591_);
v___x_593_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_594_ = ((lean_object*)(l_Lean_mkSimpleFnCall___closed__1));
v___x_595_ = l_List_intersperseTR___redArg(v___x_594_, v_args_590_);
v___x_596_ = l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(v___x_593_, v___x_595_);
lean_dec(v___x_595_);
v___x_597_ = lean_string_append(v___x_592_, v___x_596_);
lean_dec_ref(v___x_596_);
v___x_598_ = ((lean_object*)(l_Lean_mkSimpleFnCall___closed__2));
v___x_599_ = lean_string_append(v___x_597_, v___x_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend(lean_object* v_x_600_){
_start:
{
if (lean_obj_tag(v_x_600_) == 3)
{
lean_object* v___x_601_; 
v___x_601_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
return v___x_601_;
}
else
{
lean_object* v_backend_602_; 
v_backend_602_ = lean_ctor_get(v_x_600_, 0);
lean_inc(v_backend_602_);
return v_backend_602_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend___boxed(lean_object* v_x_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_ExternEntry_backend(v_x_603_);
lean_dec(v_x_603_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(lean_object* v_backend_605_, lean_object* v_x_606_){
_start:
{
if (lean_obj_tag(v_x_606_) == 0)
{
lean_object* v___x_607_; 
v___x_607_ = lean_box(0);
return v___x_607_;
}
else
{
lean_object* v_head_608_; lean_object* v_tail_609_; uint8_t v___y_611_; lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v_head_608_ = lean_ctor_get(v_x_606_, 0);
v_tail_609_ = lean_ctor_get(v_x_606_, 1);
v___x_614_ = l_Lean_ExternEntry_backend(v_head_608_);
v___x_615_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
v___x_616_ = lean_name_eq(v___x_614_, v___x_615_);
if (v___x_616_ == 0)
{
uint8_t v___x_617_; 
v___x_617_ = lean_name_eq(v___x_614_, v_backend_605_);
lean_dec(v___x_614_);
v___y_611_ = v___x_617_;
goto v___jp_610_;
}
else
{
lean_dec(v___x_614_);
v___y_611_ = v___x_616_;
goto v___jp_610_;
}
v___jp_610_:
{
if (v___y_611_ == 0)
{
v_x_606_ = v_tail_609_;
goto _start;
}
else
{
lean_object* v___x_613_; 
lean_inc(v_head_608_);
v___x_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_613_, 0, v_head_608_);
return v___x_613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0___boxed(lean_object* v_backend_618_, lean_object* v_x_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_618_, v_x_619_);
lean_dec(v_x_619_);
lean_dec(v_backend_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux(lean_object* v_backend_621_, lean_object* v_entries_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_621_, v_entries_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux___boxed(lean_object* v_backend_624_, lean_object* v_entries_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_getExternEntryForAux(v_backend_624_, v_entries_625_);
lean_dec(v_entries_625_);
lean_dec(v_backend_624_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor(lean_object* v_d_627_, lean_object* v_backend_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_628_, v_d_627_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor___boxed(lean_object* v_d_630_, lean_object* v_backend_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_getExternEntryFor(v_d_630_, v_backend_631_);
lean_dec(v_backend_631_);
lean_dec(v_d_630_);
return v_res_632_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExtern(lean_object* v_env_633_, lean_object* v_fn_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_getExternAttrData_x3f(v_env_633_, v_fn_634_);
if (lean_obj_tag(v___x_635_) == 0)
{
uint8_t v___x_636_; 
v___x_636_ = 0;
return v___x_636_;
}
else
{
uint8_t v___x_637_; 
lean_dec_ref_known(v___x_635_, 1);
v___x_637_ = 1;
return v___x_637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExtern___boxed(lean_object* v_env_638_, lean_object* v_fn_639_){
_start:
{
uint8_t v_res_640_; lean_object* v_r_641_; 
v_res_640_ = l_Lean_isExtern(v_env_638_, v_fn_639_);
v_r_641_ = lean_box(v_res_640_);
return v_r_641_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExternC(lean_object* v_env_642_, lean_object* v_fn_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_getExternAttrData_x3f(v_env_642_, v_fn_643_);
if (lean_obj_tag(v___x_644_) == 1)
{
lean_object* v_val_645_; 
v_val_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_val_645_);
lean_dec_ref_known(v___x_644_, 1);
if (lean_obj_tag(v_val_645_) == 1)
{
lean_object* v_head_646_; 
v_head_646_ = lean_ctor_get(v_val_645_, 0);
if (lean_obj_tag(v_head_646_) == 2)
{
lean_object* v_backend_647_; 
v_backend_647_ = lean_ctor_get(v_head_646_, 0);
lean_inc(v_backend_647_);
if (lean_obj_tag(v_backend_647_) == 1)
{
lean_object* v_pre_648_; 
v_pre_648_ = lean_ctor_get(v_backend_647_, 0);
if (lean_obj_tag(v_pre_648_) == 0)
{
lean_object* v_tail_649_; lean_object* v_str_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v_tail_649_ = lean_ctor_get(v_val_645_, 1);
lean_inc(v_tail_649_);
lean_dec_ref_known(v_val_645_, 2);
v_str_650_ = lean_ctor_get(v_backend_647_, 1);
lean_inc_ref(v_str_650_);
lean_dec_ref_known(v_backend_647_, 2);
v___x_651_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__2));
v___x_652_ = lean_string_dec_eq(v_str_650_, v___x_651_);
lean_dec_ref(v_str_650_);
if (v___x_652_ == 0)
{
lean_dec(v_tail_649_);
return v___x_652_;
}
else
{
if (lean_obj_tag(v_tail_649_) == 0)
{
return v___x_652_;
}
else
{
uint8_t v___x_653_; 
lean_dec(v_tail_649_);
v___x_653_ = 0;
return v___x_653_;
}
}
}
else
{
uint8_t v___x_654_; 
lean_dec_ref_known(v_backend_647_, 2);
lean_dec_ref_known(v_val_645_, 2);
v___x_654_ = 0;
return v___x_654_;
}
}
else
{
uint8_t v___x_655_; 
lean_dec(v_backend_647_);
lean_dec_ref_known(v_val_645_, 2);
v___x_655_ = 0;
return v___x_655_;
}
}
else
{
uint8_t v___x_656_; 
lean_dec_ref_known(v_val_645_, 2);
v___x_656_ = 0;
return v___x_656_;
}
}
else
{
uint8_t v___x_657_; 
lean_dec(v_val_645_);
v___x_657_ = 0;
return v___x_657_;
}
}
else
{
uint8_t v___x_658_; 
lean_dec(v___x_644_);
v___x_658_ = 0;
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExternC___boxed(lean_object* v_env_659_, lean_object* v_fn_660_){
_start:
{
uint8_t v_res_661_; lean_object* v_r_662_; 
v_res_661_ = l_Lean_isExternC(v_env_659_, v_fn_660_);
v_r_662_ = lean_box(v_res_661_);
return v_r_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternNameFor(lean_object* v_env_663_, lean_object* v_backend_664_, lean_object* v_fn_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_getExternAttrData_x3f(v_env_663_, v_fn_665_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v___x_667_; 
v___x_667_ = lean_box(0);
return v___x_667_;
}
else
{
lean_object* v_val_668_; lean_object* v___x_669_; 
v_val_668_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_val_668_);
lean_dec_ref_known(v___x_666_, 1);
v___x_669_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_664_, v_val_668_);
lean_dec(v_val_668_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v___x_670_; 
v___x_670_ = lean_box(0);
return v___x_670_;
}
else
{
lean_object* v_val_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_680_; 
v_val_671_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_680_ == 0)
{
v___x_673_ = v___x_669_;
v_isShared_674_ = v_isSharedCheck_680_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_val_671_);
lean_dec(v___x_669_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_680_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
if (lean_obj_tag(v_val_671_) == 2)
{
lean_object* v_fn_675_; lean_object* v___x_677_; 
v_fn_675_ = lean_ctor_get(v_val_671_, 1);
lean_inc_ref(v_fn_675_);
lean_dec_ref_known(v_val_671_, 2);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v_fn_675_);
v___x_677_ = v___x_673_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_fn_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
else
{
lean_object* v___x_679_; 
lean_del_object(v___x_673_);
lean_dec(v_val_671_);
v___x_679_ = lean_box(0);
return v___x_679_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExternNameFor___boxed(lean_object* v_env_681_, lean_object* v_backend_682_, lean_object* v_fn_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_getExternNameFor(v_env_681_, v_backend_682_, v_fn_683_);
lean_dec(v_backend_682_);
return v_res_684_;
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
