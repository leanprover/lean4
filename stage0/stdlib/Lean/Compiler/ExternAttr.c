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
lean_object* v___x_196_; lean_object* v_toCold_197_; lean_object* v_env_198_; lean_object* v_options_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_196_ = lean_st_ref_get(v___y_194_);
v_toCold_197_ = lean_ctor_get(v___y_193_, 0);
v_env_198_ = lean_ctor_get(v___x_196_, 0);
lean_inc_ref(v_env_198_);
lean_dec(v___x_196_);
v_options_199_ = lean_ctor_get(v_toCold_197_, 2);
v___x_200_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2);
v___x_201_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_199_);
v___x_202_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_202_, 0, v_env_198_);
lean_ctor_set(v___x_202_, 1, v___x_200_);
lean_ctor_set(v___x_202_, 2, v___x_201_);
lean_ctor_set(v___x_202_, 3, v_options_199_);
v___x_203_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v_msgData_192_);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1(v_msgData_205_, v___y_206_, v___y_207_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(lean_object* v_msg_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_ref_214_; lean_object* v___x_215_; lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_224_; 
v_ref_214_ = lean_ctor_get(v___y_211_, 2);
v___x_215_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1(v_msg_210_, v___y_211_, v___y_212_);
v_a_216_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_224_ == 0)
{
v___x_218_ = v___x_215_;
v_isShared_219_ = v_isSharedCheck_224_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_215_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_224_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_220_; lean_object* v___x_222_; 
lean_inc(v_ref_214_);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v_ref_214_);
lean_ctor_set(v___x_220_, 1, v_a_216_);
if (v_isShared_219_ == 0)
{
lean_ctor_set_tag(v___x_218_, 1);
lean_ctor_set(v___x_218_, 0, v___x_220_);
v___x_222_ = v___x_218_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg___boxed(lean_object* v_msg_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(lean_object* v_ref_230_, lean_object* v_msg_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_toCold_235_; lean_object* v_currRecDepth_236_; lean_object* v_ref_237_; uint8_t v_diag_238_; uint8_t v_suppressElabErrors_239_; lean_object* v_ref_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v_toCold_235_ = lean_ctor_get(v___y_232_, 0);
v_currRecDepth_236_ = lean_ctor_get(v___y_232_, 1);
v_ref_237_ = lean_ctor_get(v___y_232_, 2);
v_diag_238_ = lean_ctor_get_uint8(v___y_232_, sizeof(void*)*3);
v_suppressElabErrors_239_ = lean_ctor_get_uint8(v___y_232_, sizeof(void*)*3 + 1);
v_ref_240_ = l_Lean_replaceRef(v_ref_230_, v_ref_237_);
lean_inc(v_currRecDepth_236_);
lean_inc_ref(v_toCold_235_);
v___x_241_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_241_, 0, v_toCold_235_);
lean_ctor_set(v___x_241_, 1, v_currRecDepth_236_);
lean_ctor_set(v___x_241_, 2, v_ref_240_);
lean_ctor_set_uint8(v___x_241_, sizeof(void*)*3, v_diag_238_);
lean_ctor_set_uint8(v___x_241_, sizeof(void*)*3 + 1, v_suppressElabErrors_239_);
v___x_242_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_231_, v___x_241_, v___y_233_);
lean_dec_ref_known(v___x_241_, 3);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg___boxed(lean_object* v_ref_243_, lean_object* v_msg_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v_ref_243_, v_msg_244_, v___y_245_, v___y_246_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v_ref_243_);
return v_res_248_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__0));
v___x_251_ = l_Lean_stringToMessageData(v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(lean_object* v_as_255_, size_t v_sz_256_, size_t v_i_257_, lean_object* v_b_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_a_263_; uint8_t v___x_267_; 
v___x_267_ = lean_usize_dec_lt(v_i_257_, v_sz_256_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v_b_258_);
return v___x_268_;
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v_a_271_; lean_object* v___y_273_; lean_object* v_str_274_; lean_object* v___y_282_; lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_269_ = lean_unsigned_to_nat(1u);
v___x_270_ = lean_unsigned_to_nat(0u);
v_a_271_ = lean_array_uget_borrowed(v_as_255_, v_i_257_);
v___x_298_ = l_Lean_Syntax_getArg(v_a_271_, v___x_270_);
v___x_299_ = l_Lean_Syntax_isNone(v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = l_Lean_Syntax_getArg(v___x_298_, v___x_270_);
lean_dec(v___x_298_);
v___x_301_ = l_Lean_Syntax_getId(v___x_300_);
lean_dec(v___x_300_);
v___y_282_ = v___x_301_;
goto v___jp_281_;
}
else
{
lean_object* v___x_302_; 
lean_dec(v___x_298_);
v___x_302_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
v___y_282_ = v___x_302_;
goto v___jp_281_;
}
v___jp_272_:
{
lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_275_ = l_Lean_Syntax_getArg(v_a_271_, v___x_269_);
v___x_276_ = l_Lean_Syntax_isNone(v___x_275_);
lean_dec(v___x_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_277_, 0, v___y_273_);
lean_ctor_set(v___x_277_, 1, v_str_274_);
v___x_278_ = lean_array_push(v_b_258_, v___x_277_);
v_a_263_ = v___x_278_;
goto v___jp_262_;
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_279_, 0, v___y_273_);
lean_ctor_set(v___x_279_, 1, v_str_274_);
v___x_280_ = lean_array_push(v_b_258_, v___x_279_);
v_a_263_ = v___x_280_;
goto v___jp_262_;
}
}
v___jp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_unsigned_to_nat(2u);
v___x_284_ = l_Lean_Syntax_getArg(v_a_271_, v___x_283_);
v___x_285_ = l_Lean_Syntax_isStrLit_x3f(v___x_284_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1);
v___x_287_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v___x_284_, v___x_286_, v___y_259_, v___y_260_);
lean_dec(v___x_284_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_a_288_);
lean_dec_ref_known(v___x_287_, 1);
v___y_273_ = v___y_282_;
v_str_274_ = v_a_288_;
goto v___jp_272_;
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_dec(v___y_282_);
lean_dec_ref(v_b_258_);
v_a_289_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_287_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_287_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
else
{
lean_object* v_val_297_; 
lean_dec(v___x_284_);
v_val_297_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_val_297_);
lean_dec_ref_known(v___x_285_, 1);
v___y_273_ = v___y_282_;
v_str_274_ = v_val_297_;
goto v___jp_272_;
}
}
}
v___jp_262_:
{
size_t v___x_264_; size_t v___x_265_; 
v___x_264_ = ((size_t)1ULL);
v___x_265_ = lean_usize_add(v_i_257_, v___x_264_);
v_i_257_ = v___x_265_;
v_b_258_ = v_a_263_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___boxed(lean_object* v_as_303_, lean_object* v_sz_304_, lean_object* v_i_305_, lean_object* v_b_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
size_t v_sz_boxed_310_; size_t v_i_boxed_311_; lean_object* v_res_312_; 
v_sz_boxed_310_ = lean_unbox_usize(v_sz_304_);
lean_dec(v_sz_304_);
v_i_boxed_311_ = lean_unbox_usize(v_i_305_);
lean_dec(v_i_305_);
v_res_312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(v_as_303_, v_sz_boxed_310_, v_i_boxed_311_, v_b_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec_ref(v_as_303_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(lean_object* v_stx_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v_entriesStx_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_324_ = lean_unsigned_to_nat(1u);
v___x_325_ = l_Lean_Syntax_getArg(v_stx_320_, v___x_324_);
v_entriesStx_326_ = l_Lean_Syntax_getArgs(v___x_325_);
lean_dec(v___x_325_);
v___x_327_ = lean_array_get_size(v_entriesStx_326_);
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = lean_nat_dec_eq(v___x_327_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v_entries_330_; size_t v_sz_331_; size_t v___x_332_; lean_object* v___x_333_; 
v_entries_330_ = ((lean_object*)(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__0));
v_sz_331_ = lean_array_size(v_entriesStx_326_);
v___x_332_ = ((size_t)0ULL);
v___x_333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(v_entriesStx_326_, v_sz_331_, v___x_332_, v_entries_330_, v_a_321_, v_a_322_);
lean_dec_ref(v_entriesStx_326_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_342_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_342_ == 0)
{
v___x_336_ = v___x_333_;
v_isShared_337_ = v_isSharedCheck_342_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_342_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_338_ = lean_array_to_list(v_a_334_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_338_);
v___x_340_ = v___x_336_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
v_a_343_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_333_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_333_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
else
{
lean_object* v___x_351_; lean_object* v___x_352_; 
lean_dec_ref(v_entriesStx_326_);
v___x_351_ = ((lean_object*)(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2));
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
return v___x_352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___boxed(lean_object* v_stx_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(v_stx_353_, v_a_354_, v_a_355_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec(v_stx_353_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(lean_object* v_00_u03b1_358_, lean_object* v_ref_359_, lean_object* v_msg_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v_ref_359_, v_msg_360_, v___y_361_, v___y_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___boxed(lean_object* v_00_u03b1_365_, lean_object* v_ref_366_, lean_object* v_msg_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(v_00_u03b1_365_, v_ref_366_, v_msg_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v_ref_366_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0(lean_object* v_00_u03b1_372_, lean_object* v_msg_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_373_, v___y_374_, v___y_375_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___boxed(lean_object* v_00_u03b1_378_, lean_object* v_msg_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0(v_00_u03b1_378_, v_msg_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(lean_object* v_x_384_, lean_object* v_stx_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(v_stx_385_, v___y_386_, v___y_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v_x_390_, lean_object* v_stx_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v_x_390_, v_stx_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v_stx_391_);
lean_dec(v_x_390_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(lean_object* v_declName_396_, lean_object* v_externAttrData_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
uint8_t v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___x_409_; lean_object* v_env_410_; uint8_t v___y_412_; uint8_t v___x_427_; 
v___x_409_ = lean_st_ref_get(v___y_399_);
v_env_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc_ref_n(v_env_410_, 2);
lean_dec(v___x_409_);
lean_inc(v_declName_396_);
v___x_427_ = l_Lean_Environment_isProjectionFn(v_env_410_, v_declName_396_);
if (v___x_427_ == 0)
{
uint8_t v___x_428_; 
lean_inc(v_declName_396_);
lean_inc_ref(v_env_410_);
v___x_428_ = l_Lean_Environment_isConstructor(v_env_410_, v_declName_396_);
v___y_412_ = v___x_428_;
goto v___jp_411_;
}
else
{
v___y_412_ = v___x_427_;
goto v___jp_411_;
}
v___jp_401_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_405_ = lean_unsigned_to_nat(1u);
v___x_406_ = lean_mk_empty_array_with_capacity(v___x_405_);
v___x_407_ = lean_array_push(v___x_406_, v_declName_396_);
v___x_408_ = l_Lean_compileDecls(v___x_407_, v___y_402_, v___y_403_, v___y_404_);
return v___x_408_;
}
v___jp_411_:
{
if (v___y_412_ == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; 
lean_dec_ref(v_env_410_);
lean_dec(v_declName_396_);
v___x_413_ = lean_box(0);
v___x_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
return v___x_414_;
}
else
{
uint8_t v___x_415_; lean_object* v___x_416_; 
v___x_415_ = 0;
lean_inc(v_declName_396_);
v___x_416_ = l_Lean_Environment_find_x3f(v_env_410_, v_declName_396_, v___x_415_);
if (lean_obj_tag(v___x_416_) == 1)
{
lean_object* v_val_417_; 
v_val_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_val_417_);
lean_dec_ref_known(v___x_416_, 1);
if (lean_obj_tag(v_val_417_) == 2)
{
lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_425_; 
lean_dec(v_declName_396_);
v_isSharedCheck_425_ = !lean_is_exclusive(v_val_417_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; 
v_unused_426_ = lean_ctor_get(v_val_417_, 0);
lean_dec(v_unused_426_);
v___x_419_ = v_val_417_;
v_isShared_420_ = v_isSharedCheck_425_;
goto v_resetjp_418_;
}
else
{
lean_dec(v_val_417_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_425_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_421_ = lean_box(0);
if (v_isShared_420_ == 0)
{
lean_ctor_set_tag(v___x_419_, 0);
lean_ctor_set(v___x_419_, 0, v___x_421_);
v___x_423_ = v___x_419_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
else
{
lean_dec(v_val_417_);
v___y_402_ = v___y_412_;
v___y_403_ = v___y_398_;
v___y_404_ = v___y_399_;
goto v___jp_401_;
}
}
else
{
lean_dec(v___x_416_);
v___y_402_ = v___y_412_;
v___y_403_ = v___y_398_;
v___y_404_ = v___y_399_;
goto v___jp_401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v_declName_429_, lean_object* v_externAttrData_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v_declName_429_, v_externAttrData_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v_externAttrData_430_);
return v_res_434_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(uint8_t v___x_435_, lean_object* v_env_436_, lean_object* v_n_437_, lean_object* v_x_438_){
_start:
{
uint8_t v___x_439_; 
v___x_439_ = l_Lean_Environment_contains(v_env_436_, v_n_437_, v___x_435_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v___x_440_, lean_object* v_env_441_, lean_object* v_n_442_, lean_object* v_x_443_){
_start:
{
uint8_t v___x_560__boxed_444_; uint8_t v_res_445_; lean_object* v_r_446_; 
v___x_560__boxed_444_ = lean_unbox(v___x_440_);
v_res_445_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v___x_560__boxed_444_, v_env_441_, v_n_442_, v_x_443_);
lean_dec(v_x_443_);
v_r_446_ = lean_box(v_res_445_);
return v_r_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = ((lean_object*)(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_));
v___x_474_ = l_Lean_registerParametricAttribute___redArg(v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_();
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternAttrData_x3f(lean_object* v_env_477_, lean_object* v_n_478_){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = lean_box(0);
v___x_480_ = l_Lean_externAttr;
v___x_481_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_479_, v___x_480_, v_env_477_, v_n_478_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(lean_object* v_pattern_482_, lean_object* v_it_483_, lean_object* v_r_484_){
_start:
{
lean_object* v_str_485_; lean_object* v_startInclusive_486_; lean_object* v_endExclusive_487_; lean_object* v___x_488_; uint8_t v_decide_489_; 
v_str_485_ = lean_ctor_get(v_pattern_482_, 0);
v_startInclusive_486_ = lean_ctor_get(v_pattern_482_, 1);
v_endExclusive_487_ = lean_ctor_get(v_pattern_482_, 2);
v___x_488_ = lean_nat_sub(v_endExclusive_487_, v_startInclusive_486_);
v_decide_489_ = lean_nat_dec_eq(v_it_483_, v___x_488_);
lean_dec(v___x_488_);
if (v_decide_489_ == 0)
{
lean_object* v___x_490_; uint32_t v_c_491_; uint32_t v___x_492_; uint8_t v___x_493_; 
v___x_490_ = lean_nat_add(v_startInclusive_486_, v_it_483_);
v_c_491_ = lean_string_utf8_get_fast(v_str_485_, v___x_490_);
v___x_492_ = 48;
v___x_493_ = lean_uint32_dec_le(v___x_492_, v_c_491_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; 
lean_dec(v___x_490_);
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v_it_483_);
lean_ctor_set(v___x_494_, 1, v_r_484_);
return v___x_494_;
}
else
{
uint32_t v___x_495_; uint8_t v___x_496_; 
v___x_495_ = 57;
v___x_496_ = lean_uint32_dec_le(v_c_491_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; 
lean_dec(v___x_490_);
v___x_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_497_, 0, v_it_483_);
lean_ctor_set(v___x_497_, 1, v_r_484_);
return v___x_497_;
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec(v_it_483_);
v___x_498_ = lean_string_utf8_next_fast(v_str_485_, v___x_490_);
lean_dec(v___x_490_);
v___x_499_ = lean_nat_sub(v___x_498_, v_startInclusive_486_);
v___x_500_ = lean_unsigned_to_nat(10u);
v___x_501_ = lean_nat_mul(v_r_484_, v___x_500_);
lean_dec(v_r_484_);
v___x_502_ = lean_uint32_to_nat(v_c_491_);
v___x_503_ = lean_unsigned_to_nat(48u);
v___x_504_ = lean_nat_sub(v___x_502_, v___x_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_nat_add(v___x_501_, v___x_504_);
lean_dec(v___x_504_);
lean_dec(v___x_501_);
v_it_483_ = v___x_499_;
v_r_484_ = v___x_505_;
goto _start;
}
}
}
else
{
lean_object* v___x_507_; 
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v_it_483_);
lean_ctor_set(v___x_507_, 1, v_r_484_);
return v___x_507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum___boxed(lean_object* v_pattern_508_, lean_object* v_it_509_, lean_object* v_r_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(v_pattern_508_, v_it_509_, v_r_510_);
lean_dec_ref(v_pattern_508_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux(lean_object* v_args_513_, lean_object* v_pattern_514_, lean_object* v_it_515_, lean_object* v_r_516_){
_start:
{
lean_object* v___x_517_; uint8_t v_decide_518_; 
v___x_517_ = lean_string_utf8_byte_size(v_pattern_514_);
v_decide_518_ = lean_nat_dec_eq(v_it_515_, v___x_517_);
if (v_decide_518_ == 0)
{
uint32_t v_c_519_; uint32_t v___x_524_; uint8_t v___x_525_; 
v_c_519_ = lean_string_utf8_get_fast(v_pattern_514_, v_it_515_);
v___x_524_ = 35;
v___x_525_ = lean_uint32_dec_eq(v_c_519_, v___x_524_);
if (v___x_525_ == 0)
{
goto v___jp_520_;
}
else
{
if (v_decide_518_ == 0)
{
lean_object* v_it_u2081_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v_fst_530_; lean_object* v_snd_531_; lean_object* v___x_532_; lean_object* v_j_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_it_u2081_526_ = lean_string_utf8_next_fast(v_pattern_514_, v_it_515_);
lean_dec(v_it_515_);
lean_inc_ref(v_pattern_514_);
v___x_527_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_527_, 0, v_pattern_514_);
lean_ctor_set(v___x_527_, 1, v_it_u2081_526_);
lean_ctor_set(v___x_527_, 2, v___x_517_);
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(v___x_527_, v___x_528_, v___x_528_);
lean_dec_ref_known(v___x_527_, 3);
v_fst_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_fst_530_);
v_snd_531_ = lean_ctor_get(v___x_529_, 1);
lean_inc(v_snd_531_);
lean_dec_ref(v___x_529_);
v___x_532_ = lean_unsigned_to_nat(1u);
v_j_533_ = lean_nat_sub(v_snd_531_, v___x_532_);
lean_dec(v_snd_531_);
v___x_534_ = lean_nat_add(v_it_u2081_526_, v_fst_530_);
lean_dec(v_fst_530_);
v___x_535_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_536_ = l_List_getD___redArg(v_args_513_, v_j_533_, v___x_535_);
v___x_537_ = lean_string_append(v_r_516_, v___x_536_);
lean_dec(v___x_536_);
v_it_515_ = v___x_534_;
v_r_516_ = v___x_537_;
goto _start;
}
else
{
goto v___jp_520_;
}
}
v___jp_520_:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_string_utf8_next_fast(v_pattern_514_, v_it_515_);
lean_dec(v_it_515_);
v___x_522_ = lean_string_push(v_r_516_, v_c_519_);
v_it_515_ = v___x_521_;
v_r_516_ = v___x_522_;
goto _start;
}
}
else
{
lean_dec(v_it_515_);
lean_dec_ref(v_pattern_514_);
return v_r_516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux___boxed(lean_object* v_args_539_, lean_object* v_pattern_540_, lean_object* v_it_541_, lean_object* v_r_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_expandExternPatternAux(v_args_539_, v_pattern_540_, v_it_541_, v_r_542_);
lean_dec(v_args_539_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter___redArg(lean_object* v_x_544_, lean_object* v_h__1_545_){
_start:
{
lean_object* v_fst_546_; lean_object* v_snd_547_; lean_object* v___x_548_; 
v_fst_546_ = lean_ctor_get(v_x_544_, 0);
lean_inc(v_fst_546_);
v_snd_547_ = lean_ctor_get(v_x_544_, 1);
lean_inc(v_snd_547_);
lean_dec_ref(v_x_544_);
v___x_548_ = lean_apply_2(v_h__1_545_, v_fst_546_, v_snd_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter(lean_object* v_pattern_549_, lean_object* v_it_u2081_550_, lean_object* v_motive_551_, lean_object* v_x_552_, lean_object* v_h__1_553_){
_start:
{
lean_object* v_fst_554_; lean_object* v_snd_555_; lean_object* v___x_556_; 
v_fst_554_ = lean_ctor_get(v_x_552_, 0);
lean_inc(v_fst_554_);
v_snd_555_ = lean_ctor_get(v_x_552_, 1);
lean_inc(v_snd_555_);
lean_dec_ref(v_x_552_);
v___x_556_ = lean_apply_2(v_h__1_553_, v_fst_554_, v_snd_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter___boxed(lean_object* v_pattern_557_, lean_object* v_it_u2081_558_, lean_object* v_motive_559_, lean_object* v_x_560_, lean_object* v_h__1_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter(v_pattern_557_, v_it_u2081_558_, v_motive_559_, v_x_560_, v_h__1_561_);
lean_dec(v_it_u2081_558_);
lean_dec_ref(v_pattern_557_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPattern(lean_object* v_pattern_563_, lean_object* v_args_564_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_567_ = l_Lean_expandExternPatternAux(v_args_564_, v_pattern_563_, v___x_565_, v___x_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPattern___boxed(lean_object* v_pattern_568_, lean_object* v_args_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_expandExternPattern(v_pattern_568_, v_args_569_);
lean_dec(v_args_569_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(lean_object* v_x_571_, lean_object* v_x_572_){
_start:
{
if (lean_obj_tag(v_x_572_) == 0)
{
return v_x_571_;
}
else
{
lean_object* v_head_573_; lean_object* v_tail_574_; lean_object* v___x_575_; 
v_head_573_ = lean_ctor_get(v_x_572_, 0);
v_tail_574_ = lean_ctor_get(v_x_572_, 1);
v___x_575_ = lean_string_append(v_x_571_, v_head_573_);
v_x_571_ = v___x_575_;
v_x_572_ = v_tail_574_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0___boxed(lean_object* v_x_577_, lean_object* v_x_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(v_x_577_, v_x_578_);
lean_dec(v_x_578_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleFnCall(lean_object* v_fn_583_, lean_object* v_args_584_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_585_ = ((lean_object*)(l_Lean_mkSimpleFnCall___closed__0));
v___x_586_ = lean_string_append(v_fn_583_, v___x_585_);
v___x_587_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_588_ = ((lean_object*)(l_Lean_mkSimpleFnCall___closed__1));
v___x_589_ = l_List_intersperseTR___redArg(v___x_588_, v_args_584_);
v___x_590_ = l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(v___x_587_, v___x_589_);
lean_dec(v___x_589_);
v___x_591_ = lean_string_append(v___x_586_, v___x_590_);
lean_dec_ref(v___x_590_);
v___x_592_ = ((lean_object*)(l_Lean_mkSimpleFnCall___closed__2));
v___x_593_ = lean_string_append(v___x_591_, v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend(lean_object* v_x_594_){
_start:
{
if (lean_obj_tag(v_x_594_) == 3)
{
lean_object* v___x_595_; 
v___x_595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
return v___x_595_;
}
else
{
lean_object* v_backend_596_; 
v_backend_596_ = lean_ctor_get(v_x_594_, 0);
lean_inc(v_backend_596_);
return v_backend_596_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend___boxed(lean_object* v_x_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_ExternEntry_backend(v_x_597_);
lean_dec(v_x_597_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(lean_object* v_backend_599_, lean_object* v_x_600_){
_start:
{
if (lean_obj_tag(v_x_600_) == 0)
{
lean_object* v___x_601_; 
v___x_601_ = lean_box(0);
return v___x_601_;
}
else
{
lean_object* v_head_602_; lean_object* v_tail_603_; uint8_t v___y_605_; lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v_head_602_ = lean_ctor_get(v_x_600_, 0);
v_tail_603_ = lean_ctor_get(v_x_600_, 1);
v___x_608_ = l_Lean_ExternEntry_backend(v_head_602_);
v___x_609_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
v___x_610_ = lean_name_eq(v___x_608_, v___x_609_);
if (v___x_610_ == 0)
{
uint8_t v___x_611_; 
v___x_611_ = lean_name_eq(v___x_608_, v_backend_599_);
lean_dec(v___x_608_);
v___y_605_ = v___x_611_;
goto v___jp_604_;
}
else
{
lean_dec(v___x_608_);
v___y_605_ = v___x_610_;
goto v___jp_604_;
}
v___jp_604_:
{
if (v___y_605_ == 0)
{
v_x_600_ = v_tail_603_;
goto _start;
}
else
{
lean_object* v___x_607_; 
lean_inc(v_head_602_);
v___x_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_607_, 0, v_head_602_);
return v___x_607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0___boxed(lean_object* v_backend_612_, lean_object* v_x_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_612_, v_x_613_);
lean_dec(v_x_613_);
lean_dec(v_backend_612_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux(lean_object* v_backend_615_, lean_object* v_entries_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_615_, v_entries_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux___boxed(lean_object* v_backend_618_, lean_object* v_entries_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_getExternEntryForAux(v_backend_618_, v_entries_619_);
lean_dec(v_entries_619_);
lean_dec(v_backend_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor(lean_object* v_d_621_, lean_object* v_backend_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_622_, v_d_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor___boxed(lean_object* v_d_624_, lean_object* v_backend_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_getExternEntryFor(v_d_624_, v_backend_625_);
lean_dec(v_backend_625_);
lean_dec(v_d_624_);
return v_res_626_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExtern(lean_object* v_env_627_, lean_object* v_fn_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_getExternAttrData_x3f(v_env_627_, v_fn_628_);
if (lean_obj_tag(v___x_629_) == 0)
{
uint8_t v___x_630_; 
v___x_630_ = 0;
return v___x_630_;
}
else
{
uint8_t v___x_631_; 
lean_dec_ref_known(v___x_629_, 1);
v___x_631_ = 1;
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExtern___boxed(lean_object* v_env_632_, lean_object* v_fn_633_){
_start:
{
uint8_t v_res_634_; lean_object* v_r_635_; 
v_res_634_ = l_Lean_isExtern(v_env_632_, v_fn_633_);
v_r_635_ = lean_box(v_res_634_);
return v_r_635_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExternC(lean_object* v_env_636_, lean_object* v_fn_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_getExternAttrData_x3f(v_env_636_, v_fn_637_);
if (lean_obj_tag(v___x_638_) == 1)
{
lean_object* v_val_639_; 
v_val_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_val_639_);
lean_dec_ref_known(v___x_638_, 1);
if (lean_obj_tag(v_val_639_) == 1)
{
lean_object* v_head_640_; 
v_head_640_ = lean_ctor_get(v_val_639_, 0);
if (lean_obj_tag(v_head_640_) == 2)
{
lean_object* v_backend_641_; 
v_backend_641_ = lean_ctor_get(v_head_640_, 0);
lean_inc(v_backend_641_);
if (lean_obj_tag(v_backend_641_) == 1)
{
lean_object* v_pre_642_; 
v_pre_642_ = lean_ctor_get(v_backend_641_, 0);
if (lean_obj_tag(v_pre_642_) == 0)
{
lean_object* v_tail_643_; lean_object* v_str_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_tail_643_ = lean_ctor_get(v_val_639_, 1);
lean_inc(v_tail_643_);
lean_dec_ref_known(v_val_639_, 2);
v_str_644_ = lean_ctor_get(v_backend_641_, 1);
lean_inc_ref(v_str_644_);
lean_dec_ref_known(v_backend_641_, 2);
v___x_645_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__2));
v___x_646_ = lean_string_dec_eq(v_str_644_, v___x_645_);
lean_dec_ref(v_str_644_);
if (v___x_646_ == 0)
{
lean_dec(v_tail_643_);
return v___x_646_;
}
else
{
if (lean_obj_tag(v_tail_643_) == 0)
{
return v___x_646_;
}
else
{
uint8_t v___x_647_; 
lean_dec(v_tail_643_);
v___x_647_ = 0;
return v___x_647_;
}
}
}
else
{
uint8_t v___x_648_; 
lean_dec_ref_known(v_backend_641_, 2);
lean_dec_ref_known(v_val_639_, 2);
v___x_648_ = 0;
return v___x_648_;
}
}
else
{
uint8_t v___x_649_; 
lean_dec(v_backend_641_);
lean_dec_ref_known(v_val_639_, 2);
v___x_649_ = 0;
return v___x_649_;
}
}
else
{
uint8_t v___x_650_; 
lean_dec_ref_known(v_val_639_, 2);
v___x_650_ = 0;
return v___x_650_;
}
}
else
{
uint8_t v___x_651_; 
lean_dec(v_val_639_);
v___x_651_ = 0;
return v___x_651_;
}
}
else
{
uint8_t v___x_652_; 
lean_dec(v___x_638_);
v___x_652_ = 0;
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExternC___boxed(lean_object* v_env_653_, lean_object* v_fn_654_){
_start:
{
uint8_t v_res_655_; lean_object* v_r_656_; 
v_res_655_ = l_Lean_isExternC(v_env_653_, v_fn_654_);
v_r_656_ = lean_box(v_res_655_);
return v_r_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternNameFor(lean_object* v_env_657_, lean_object* v_backend_658_, lean_object* v_fn_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_getExternAttrData_x3f(v_env_657_, v_fn_659_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v___x_661_; 
v___x_661_ = lean_box(0);
return v___x_661_;
}
else
{
lean_object* v_val_662_; lean_object* v___x_663_; 
v_val_662_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_val_662_);
lean_dec_ref_known(v___x_660_, 1);
v___x_663_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_658_, v_val_662_);
lean_dec(v_val_662_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v___x_664_; 
v___x_664_ = lean_box(0);
return v___x_664_;
}
else
{
lean_object* v_val_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_674_; 
v_val_665_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_674_ == 0)
{
v___x_667_ = v___x_663_;
v_isShared_668_ = v_isSharedCheck_674_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_val_665_);
lean_dec(v___x_663_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_674_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
if (lean_obj_tag(v_val_665_) == 2)
{
lean_object* v_fn_669_; lean_object* v___x_671_; 
v_fn_669_ = lean_ctor_get(v_val_665_, 1);
lean_inc_ref(v_fn_669_);
lean_dec_ref_known(v_val_665_, 2);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v_fn_669_);
v___x_671_ = v___x_667_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_fn_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
else
{
lean_object* v___x_673_; 
lean_del_object(v___x_667_);
lean_dec(v_val_665_);
v___x_673_ = lean_box(0);
return v___x_673_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExternNameFor___boxed(lean_object* v_env_675_, lean_object* v_backend_676_, lean_object* v_fn_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_getExternNameFor(v_env_675_, v_backend_676_, v_fn_677_);
lean_dec(v_backend_676_);
return v_res_678_;
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
