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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
v___x_178_ = lean_alloc_ctor(0, 10, 0);
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
v_options_198_ = lean_ctor_get(v___y_193_, 2);
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
v_ref_213_ = lean_ctor_get(v___y_210_, 5);
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
lean_object* v_fileName_234_; lean_object* v_fileMap_235_; lean_object* v_options_236_; lean_object* v_currRecDepth_237_; lean_object* v_maxRecDepth_238_; lean_object* v_ref_239_; lean_object* v_currNamespace_240_; lean_object* v_openDecls_241_; lean_object* v_initHeartbeats_242_; lean_object* v_maxHeartbeats_243_; lean_object* v_quotContext_244_; lean_object* v_currMacroScope_245_; uint8_t v_diag_246_; lean_object* v_cancelTk_x3f_247_; uint8_t v_suppressElabErrors_248_; lean_object* v_inheritedTraceOptions_249_; lean_object* v_ref_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_fileName_234_ = lean_ctor_get(v___y_231_, 0);
v_fileMap_235_ = lean_ctor_get(v___y_231_, 1);
v_options_236_ = lean_ctor_get(v___y_231_, 2);
v_currRecDepth_237_ = lean_ctor_get(v___y_231_, 3);
v_maxRecDepth_238_ = lean_ctor_get(v___y_231_, 4);
v_ref_239_ = lean_ctor_get(v___y_231_, 5);
v_currNamespace_240_ = lean_ctor_get(v___y_231_, 6);
v_openDecls_241_ = lean_ctor_get(v___y_231_, 7);
v_initHeartbeats_242_ = lean_ctor_get(v___y_231_, 8);
v_maxHeartbeats_243_ = lean_ctor_get(v___y_231_, 9);
v_quotContext_244_ = lean_ctor_get(v___y_231_, 10);
v_currMacroScope_245_ = lean_ctor_get(v___y_231_, 11);
v_diag_246_ = lean_ctor_get_uint8(v___y_231_, sizeof(void*)*14);
v_cancelTk_x3f_247_ = lean_ctor_get(v___y_231_, 12);
v_suppressElabErrors_248_ = lean_ctor_get_uint8(v___y_231_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_249_ = lean_ctor_get(v___y_231_, 13);
v_ref_250_ = l_Lean_replaceRef(v_ref_229_, v_ref_239_);
lean_inc_ref(v_inheritedTraceOptions_249_);
lean_inc(v_cancelTk_x3f_247_);
lean_inc(v_currMacroScope_245_);
lean_inc(v_quotContext_244_);
lean_inc(v_maxHeartbeats_243_);
lean_inc(v_initHeartbeats_242_);
lean_inc(v_openDecls_241_);
lean_inc(v_currNamespace_240_);
lean_inc(v_maxRecDepth_238_);
lean_inc(v_currRecDepth_237_);
lean_inc_ref(v_options_236_);
lean_inc_ref(v_fileMap_235_);
lean_inc_ref(v_fileName_234_);
v___x_251_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_251_, 0, v_fileName_234_);
lean_ctor_set(v___x_251_, 1, v_fileMap_235_);
lean_ctor_set(v___x_251_, 2, v_options_236_);
lean_ctor_set(v___x_251_, 3, v_currRecDepth_237_);
lean_ctor_set(v___x_251_, 4, v_maxRecDepth_238_);
lean_ctor_set(v___x_251_, 5, v_ref_250_);
lean_ctor_set(v___x_251_, 6, v_currNamespace_240_);
lean_ctor_set(v___x_251_, 7, v_openDecls_241_);
lean_ctor_set(v___x_251_, 8, v_initHeartbeats_242_);
lean_ctor_set(v___x_251_, 9, v_maxHeartbeats_243_);
lean_ctor_set(v___x_251_, 10, v_quotContext_244_);
lean_ctor_set(v___x_251_, 11, v_currMacroScope_245_);
lean_ctor_set(v___x_251_, 12, v_cancelTk_x3f_247_);
lean_ctor_set(v___x_251_, 13, v_inheritedTraceOptions_249_);
lean_ctor_set_uint8(v___x_251_, sizeof(void*)*14, v_diag_246_);
lean_ctor_set_uint8(v___x_251_, sizeof(void*)*14 + 1, v_suppressElabErrors_248_);
v___x_252_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_230_, v___x_251_, v___y_232_);
lean_dec_ref_known(v___x_251_, 14);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg___boxed(lean_object* v_ref_253_, lean_object* v_msg_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v_ref_253_, v_msg_254_, v___y_255_, v___y_256_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v_ref_253_);
return v_res_258_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__0));
v___x_261_ = l_Lean_stringToMessageData(v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(lean_object* v_as_265_, size_t v_sz_266_, size_t v_i_267_, lean_object* v_b_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_a_273_; uint8_t v___x_277_; 
v___x_277_ = lean_usize_dec_lt(v_i_267_, v_sz_266_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; 
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v_b_268_);
return v___x_278_;
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v_a_281_; lean_object* v___y_283_; lean_object* v_str_284_; lean_object* v___y_292_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_279_ = lean_unsigned_to_nat(1u);
v___x_280_ = lean_unsigned_to_nat(0u);
v_a_281_ = lean_array_uget_borrowed(v_as_265_, v_i_267_);
v___x_308_ = l_Lean_Syntax_getArg(v_a_281_, v___x_280_);
v___x_309_ = l_Lean_Syntax_isNone(v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = l_Lean_Syntax_getArg(v___x_308_, v___x_280_);
lean_dec(v___x_308_);
v___x_311_ = l_Lean_Syntax_getId(v___x_310_);
lean_dec(v___x_310_);
v___y_292_ = v___x_311_;
goto v___jp_291_;
}
else
{
lean_object* v___x_312_; 
lean_dec(v___x_308_);
v___x_312_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
v___y_292_ = v___x_312_;
goto v___jp_291_;
}
v___jp_282_:
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = l_Lean_Syntax_getArg(v_a_281_, v___x_279_);
v___x_286_ = l_Lean_Syntax_isNone(v___x_285_);
lean_dec(v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_287_, 0, v___y_283_);
lean_ctor_set(v___x_287_, 1, v_str_284_);
v___x_288_ = lean_array_push(v_b_268_, v___x_287_);
v_a_273_ = v___x_288_;
goto v___jp_272_;
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_289_, 0, v___y_283_);
lean_ctor_set(v___x_289_, 1, v_str_284_);
v___x_290_ = lean_array_push(v_b_268_, v___x_289_);
v_a_273_ = v___x_290_;
goto v___jp_272_;
}
}
v___jp_291_:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = lean_unsigned_to_nat(2u);
v___x_294_ = l_Lean_Syntax_getArg(v_a_281_, v___x_293_);
v___x_295_ = l_Lean_Syntax_isStrLit_x3f(v___x_294_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1);
v___x_297_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v___x_294_, v___x_296_, v___y_269_, v___y_270_);
lean_dec(v___x_294_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_a_298_);
lean_dec_ref_known(v___x_297_, 1);
v___y_283_ = v___y_292_;
v_str_284_ = v_a_298_;
goto v___jp_282_;
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_dec(v___y_292_);
lean_dec_ref(v_b_268_);
v_a_299_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_297_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_297_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
else
{
lean_object* v_val_307_; 
lean_dec(v___x_294_);
v_val_307_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_val_307_);
lean_dec_ref_known(v___x_295_, 1);
v___y_283_ = v___y_292_;
v_str_284_ = v_val_307_;
goto v___jp_282_;
}
}
}
v___jp_272_:
{
size_t v___x_274_; size_t v___x_275_; 
v___x_274_ = ((size_t)1ULL);
v___x_275_ = lean_usize_add(v_i_267_, v___x_274_);
v_i_267_ = v___x_275_;
v_b_268_ = v_a_273_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___boxed(lean_object* v_as_313_, lean_object* v_sz_314_, lean_object* v_i_315_, lean_object* v_b_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
size_t v_sz_boxed_320_; size_t v_i_boxed_321_; lean_object* v_res_322_; 
v_sz_boxed_320_ = lean_unbox_usize(v_sz_314_);
lean_dec(v_sz_314_);
v_i_boxed_321_ = lean_unbox_usize(v_i_315_);
lean_dec(v_i_315_);
v_res_322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(v_as_313_, v_sz_boxed_320_, v_i_boxed_321_, v_b_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec_ref(v_as_313_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(lean_object* v_stx_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v_entriesStx_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_334_ = lean_unsigned_to_nat(1u);
v___x_335_ = l_Lean_Syntax_getArg(v_stx_330_, v___x_334_);
v_entriesStx_336_ = l_Lean_Syntax_getArgs(v___x_335_);
lean_dec(v___x_335_);
v___x_337_ = lean_array_get_size(v_entriesStx_336_);
v___x_338_ = lean_unsigned_to_nat(0u);
v___x_339_ = lean_nat_dec_eq(v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v_entries_340_; size_t v_sz_341_; size_t v___x_342_; lean_object* v___x_343_; 
v_entries_340_ = ((lean_object*)(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__0));
v_sz_341_ = lean_array_size(v_entriesStx_336_);
v___x_342_ = ((size_t)0ULL);
v___x_343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(v_entriesStx_336_, v_sz_341_, v___x_342_, v_entries_340_, v_a_331_, v_a_332_);
lean_dec_ref(v_entriesStx_336_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_352_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_352_ == 0)
{
v___x_346_ = v___x_343_;
v_isShared_347_ = v_isSharedCheck_352_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_352_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_348_ = lean_array_to_list(v_a_344_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_348_);
v___x_350_ = v___x_346_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
else
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
v_a_353_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_343_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_343_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; 
lean_dec_ref(v_entriesStx_336_);
v___x_361_ = ((lean_object*)(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2));
v___x_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___boxed(lean_object* v_stx_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(v_stx_363_, v_a_364_, v_a_365_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_stx_363_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(lean_object* v_00_u03b1_368_, lean_object* v_ref_369_, lean_object* v_msg_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v_ref_369_, v_msg_370_, v___y_371_, v___y_372_);
return v___x_374_;
}
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0(lean_object* v_00_u03b1_382_, lean_object* v_msg_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_383_, v___y_384_, v___y_385_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___boxed(lean_object* v_00_u03b1_388_, lean_object* v_msg_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0(v_00_u03b1_388_, v_msg_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(lean_object* v_x_394_, lean_object* v_stx_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(v_stx_395_, v___y_396_, v___y_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v_x_400_, lean_object* v_stx_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v_x_400_, v_stx_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v_stx_401_);
lean_dec(v_x_400_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(lean_object* v_declName_406_, lean_object* v_externAttrData_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
uint8_t v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___x_419_; lean_object* v_env_420_; uint8_t v___y_422_; uint8_t v___x_437_; 
v___x_419_ = lean_st_ref_get(v___y_409_);
v_env_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc_ref_n(v_env_420_, 2);
lean_dec(v___x_419_);
lean_inc(v_declName_406_);
v___x_437_ = l_Lean_Environment_isProjectionFn(v_env_420_, v_declName_406_);
if (v___x_437_ == 0)
{
uint8_t v___x_438_; 
lean_inc(v_declName_406_);
lean_inc_ref(v_env_420_);
v___x_438_ = l_Lean_Environment_isConstructor(v_env_420_, v_declName_406_);
v___y_422_ = v___x_438_;
goto v___jp_421_;
}
else
{
v___y_422_ = v___x_437_;
goto v___jp_421_;
}
v___jp_411_:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_415_ = lean_unsigned_to_nat(1u);
v___x_416_ = lean_mk_empty_array_with_capacity(v___x_415_);
v___x_417_ = lean_array_push(v___x_416_, v_declName_406_);
v___x_418_ = l_Lean_compileDecls(v___x_417_, v___y_412_, v___y_413_, v___y_414_);
return v___x_418_;
}
v___jp_421_:
{
if (v___y_422_ == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec_ref(v_env_420_);
lean_dec(v_declName_406_);
v___x_423_ = lean_box(0);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
else
{
uint8_t v___x_425_; lean_object* v___x_426_; 
v___x_425_ = 0;
lean_inc(v_declName_406_);
v___x_426_ = l_Lean_Environment_find_x3f(v_env_420_, v_declName_406_, v___x_425_);
if (lean_obj_tag(v___x_426_) == 1)
{
lean_object* v_val_427_; 
v_val_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_val_427_);
lean_dec_ref_known(v___x_426_, 1);
if (lean_obj_tag(v_val_427_) == 2)
{
lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_435_; 
lean_dec(v_declName_406_);
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
v___y_412_ = v___y_422_;
v___y_413_ = v___y_408_;
v___y_414_ = v___y_409_;
goto v___jp_411_;
}
}
else
{
lean_dec(v___x_426_);
v___y_412_ = v___y_422_;
v___y_413_ = v___y_408_;
v___y_414_ = v___y_409_;
goto v___jp_411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v_declName_439_, lean_object* v_externAttrData_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v_declName_439_, v_externAttrData_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v_externAttrData_440_);
return v_res_444_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(uint8_t v___x_445_, lean_object* v_env_446_, lean_object* v_n_447_, lean_object* v_x_448_){
_start:
{
uint8_t v___x_449_; 
v___x_449_ = l_Lean_Environment_contains(v_env_446_, v_n_447_, v___x_445_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v___x_450_, lean_object* v_env_451_, lean_object* v_n_452_, lean_object* v_x_453_){
_start:
{
uint8_t v___x_632__boxed_454_; uint8_t v_res_455_; lean_object* v_r_456_; 
v___x_632__boxed_454_ = lean_unbox(v___x_450_);
v_res_455_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v___x_632__boxed_454_, v_env_451_, v_n_452_, v_x_453_);
lean_dec(v_x_453_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = ((lean_object*)(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_));
v___x_484_ = l_Lean_registerParametricAttribute___redArg(v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v_a_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_();
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternAttrData_x3f(lean_object* v_env_487_, lean_object* v_n_488_){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = lean_box(0);
v___x_490_ = l_Lean_externAttr;
v___x_491_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_489_, v___x_490_, v_env_487_, v_n_488_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(lean_object* v_pattern_492_, lean_object* v_it_493_, lean_object* v_r_494_){
_start:
{
lean_object* v_str_495_; lean_object* v_startInclusive_496_; lean_object* v_endExclusive_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v_str_495_ = lean_ctor_get(v_pattern_492_, 0);
v_startInclusive_496_ = lean_ctor_get(v_pattern_492_, 1);
v_endExclusive_497_ = lean_ctor_get(v_pattern_492_, 2);
v___x_498_ = lean_nat_sub(v_endExclusive_497_, v_startInclusive_496_);
v___x_499_ = lean_nat_dec_eq(v_it_493_, v___x_498_);
lean_dec(v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; uint32_t v_c_501_; uint8_t v___y_503_; uint32_t v___x_514_; uint8_t v___x_515_; 
v___x_500_ = lean_nat_add(v_startInclusive_496_, v_it_493_);
v_c_501_ = lean_string_utf8_get_fast(v_str_495_, v___x_500_);
v___x_514_ = 48;
v___x_515_ = lean_uint32_dec_le(v___x_514_, v_c_501_);
if (v___x_515_ == 0)
{
v___y_503_ = v___x_515_;
goto v___jp_502_;
}
else
{
uint32_t v___x_516_; uint8_t v___x_517_; 
v___x_516_ = 57;
v___x_517_ = lean_uint32_dec_le(v_c_501_, v___x_516_);
v___y_503_ = v___x_517_;
goto v___jp_502_;
}
v___jp_502_:
{
if (v___y_503_ == 0)
{
lean_object* v___x_504_; 
lean_dec(v___x_500_);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v_it_493_);
lean_ctor_set(v___x_504_, 1, v_r_494_);
return v___x_504_;
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec(v_it_493_);
v___x_505_ = lean_string_utf8_next_fast(v_str_495_, v___x_500_);
lean_dec(v___x_500_);
v___x_506_ = lean_nat_sub(v___x_505_, v_startInclusive_496_);
v___x_507_ = lean_unsigned_to_nat(10u);
v___x_508_ = lean_nat_mul(v_r_494_, v___x_507_);
lean_dec(v_r_494_);
v___x_509_ = lean_uint32_to_nat(v_c_501_);
v___x_510_ = lean_unsigned_to_nat(48u);
v___x_511_ = lean_nat_sub(v___x_509_, v___x_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_nat_add(v___x_508_, v___x_511_);
lean_dec(v___x_511_);
lean_dec(v___x_508_);
v_it_493_ = v___x_506_;
v_r_494_ = v___x_512_;
goto _start;
}
}
}
else
{
lean_object* v___x_518_; 
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v_it_493_);
lean_ctor_set(v___x_518_, 1, v_r_494_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum___boxed(lean_object* v_pattern_519_, lean_object* v_it_520_, lean_object* v_r_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(v_pattern_519_, v_it_520_, v_r_521_);
lean_dec_ref(v_pattern_519_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux(lean_object* v_args_524_, lean_object* v_pattern_525_, lean_object* v_it_526_, lean_object* v_r_527_){
_start:
{
lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_528_ = lean_string_utf8_byte_size(v_pattern_525_);
v___x_529_ = lean_nat_dec_eq(v_it_526_, v___x_528_);
if (v___x_529_ == 0)
{
uint32_t v_c_530_; uint32_t v___x_535_; uint8_t v___x_536_; 
v_c_530_ = lean_string_utf8_get_fast(v_pattern_525_, v_it_526_);
v___x_535_ = 35;
v___x_536_ = lean_uint32_dec_eq(v_c_530_, v___x_535_);
if (v___x_536_ == 0)
{
goto v___jp_531_;
}
else
{
if (v___x_529_ == 0)
{
lean_object* v_it_u2081_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v_fst_541_; lean_object* v_snd_542_; lean_object* v___x_543_; lean_object* v_j_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v_it_u2081_537_ = lean_string_utf8_next_fast(v_pattern_525_, v_it_526_);
lean_dec(v_it_526_);
lean_inc_ref(v_pattern_525_);
v___x_538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_538_, 0, v_pattern_525_);
lean_ctor_set(v___x_538_, 1, v_it_u2081_537_);
lean_ctor_set(v___x_538_, 2, v___x_528_);
v___x_539_ = lean_unsigned_to_nat(0u);
v___x_540_ = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(v___x_538_, v___x_539_, v___x_539_);
lean_dec_ref_known(v___x_538_, 3);
v_fst_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_fst_541_);
v_snd_542_ = lean_ctor_get(v___x_540_, 1);
lean_inc(v_snd_542_);
lean_dec_ref(v___x_540_);
v___x_543_ = lean_unsigned_to_nat(1u);
v_j_544_ = lean_nat_sub(v_snd_542_, v___x_543_);
lean_dec(v_snd_542_);
v___x_545_ = lean_nat_add(v_it_u2081_537_, v_fst_541_);
lean_dec(v_fst_541_);
v___x_546_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_547_ = l_List_getD___redArg(v_args_524_, v_j_544_, v___x_546_);
v___x_548_ = lean_string_append(v_r_527_, v___x_547_);
lean_dec(v___x_547_);
v_it_526_ = v___x_545_;
v_r_527_ = v___x_548_;
goto _start;
}
else
{
goto v___jp_531_;
}
}
v___jp_531_:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_string_utf8_next_fast(v_pattern_525_, v_it_526_);
lean_dec(v_it_526_);
v___x_533_ = lean_string_push(v_r_527_, v_c_530_);
v_it_526_ = v___x_532_;
v_r_527_ = v___x_533_;
goto _start;
}
}
else
{
lean_dec(v_it_526_);
lean_dec_ref(v_pattern_525_);
return v_r_527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux___boxed(lean_object* v_args_550_, lean_object* v_pattern_551_, lean_object* v_it_552_, lean_object* v_r_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_expandExternPatternAux(v_args_550_, v_pattern_551_, v_it_552_, v_r_553_);
lean_dec(v_args_550_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter___redArg(lean_object* v_x_555_, lean_object* v_h__1_556_){
_start:
{
lean_object* v_fst_557_; lean_object* v_snd_558_; lean_object* v___x_559_; 
v_fst_557_ = lean_ctor_get(v_x_555_, 0);
lean_inc(v_fst_557_);
v_snd_558_ = lean_ctor_get(v_x_555_, 1);
lean_inc(v_snd_558_);
lean_dec_ref(v_x_555_);
v___x_559_ = lean_apply_2(v_h__1_556_, v_fst_557_, v_snd_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter(lean_object* v_pattern_560_, lean_object* v_it_u2081_561_, lean_object* v_motive_562_, lean_object* v_x_563_, lean_object* v_h__1_564_){
_start:
{
lean_object* v_fst_565_; lean_object* v_snd_566_; lean_object* v___x_567_; 
v_fst_565_ = lean_ctor_get(v_x_563_, 0);
lean_inc(v_fst_565_);
v_snd_566_ = lean_ctor_get(v_x_563_, 1);
lean_inc(v_snd_566_);
lean_dec_ref(v_x_563_);
v___x_567_ = lean_apply_2(v_h__1_564_, v_fst_565_, v_snd_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter___boxed(lean_object* v_pattern_568_, lean_object* v_it_u2081_569_, lean_object* v_motive_570_, lean_object* v_x_571_, lean_object* v_h__1_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter(v_pattern_568_, v_it_u2081_569_, v_motive_570_, v_x_571_, v_h__1_572_);
lean_dec(v_it_u2081_569_);
lean_dec_ref(v_pattern_568_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPattern(lean_object* v_pattern_574_, lean_object* v_args_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_578_ = l_Lean_expandExternPatternAux(v_args_575_, v_pattern_574_, v___x_576_, v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPattern___boxed(lean_object* v_pattern_579_, lean_object* v_args_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_expandExternPattern(v_pattern_579_, v_args_580_);
lean_dec(v_args_580_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(lean_object* v_x_582_, lean_object* v_x_583_){
_start:
{
if (lean_obj_tag(v_x_583_) == 0)
{
return v_x_582_;
}
else
{
lean_object* v_head_584_; lean_object* v_tail_585_; lean_object* v___x_586_; 
v_head_584_ = lean_ctor_get(v_x_583_, 0);
v_tail_585_ = lean_ctor_get(v_x_583_, 1);
v___x_586_ = lean_string_append(v_x_582_, v_head_584_);
v_x_582_ = v___x_586_;
v_x_583_ = v_tail_585_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0___boxed(lean_object* v_x_588_, lean_object* v_x_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(v_x_588_, v_x_589_);
lean_dec(v_x_589_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleFnCall(lean_object* v_fn_594_, lean_object* v_args_595_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_596_ = ((lean_object*)(l_Lean_mkSimpleFnCall___closed__0));
v___x_597_ = lean_string_append(v_fn_594_, v___x_596_);
v___x_598_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_599_ = ((lean_object*)(l_Lean_mkSimpleFnCall___closed__1));
v___x_600_ = l_List_intersperseTR___redArg(v___x_599_, v_args_595_);
v___x_601_ = l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(v___x_598_, v___x_600_);
lean_dec(v___x_600_);
v___x_602_ = lean_string_append(v___x_597_, v___x_601_);
lean_dec_ref(v___x_601_);
v___x_603_ = ((lean_object*)(l_Lean_mkSimpleFnCall___closed__2));
v___x_604_ = lean_string_append(v___x_602_, v___x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend(lean_object* v_x_605_){
_start:
{
if (lean_obj_tag(v_x_605_) == 3)
{
lean_object* v___x_606_; 
v___x_606_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
return v___x_606_;
}
else
{
lean_object* v_backend_607_; 
v_backend_607_ = lean_ctor_get(v_x_605_, 0);
lean_inc(v_backend_607_);
return v_backend_607_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend___boxed(lean_object* v_x_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_ExternEntry_backend(v_x_608_);
lean_dec(v_x_608_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(lean_object* v_backend_610_, lean_object* v_x_611_){
_start:
{
if (lean_obj_tag(v_x_611_) == 0)
{
lean_object* v___x_612_; 
v___x_612_ = lean_box(0);
return v___x_612_;
}
else
{
lean_object* v_head_613_; lean_object* v_tail_614_; uint8_t v___y_616_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v_head_613_ = lean_ctor_get(v_x_611_, 0);
v_tail_614_ = lean_ctor_get(v_x_611_, 1);
v___x_619_ = l_Lean_ExternEntry_backend(v_head_613_);
v___x_620_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
v___x_621_ = lean_name_eq(v___x_619_, v___x_620_);
if (v___x_621_ == 0)
{
uint8_t v___x_622_; 
v___x_622_ = lean_name_eq(v___x_619_, v_backend_610_);
lean_dec(v___x_619_);
v___y_616_ = v___x_622_;
goto v___jp_615_;
}
else
{
lean_dec(v___x_619_);
v___y_616_ = v___x_621_;
goto v___jp_615_;
}
v___jp_615_:
{
if (v___y_616_ == 0)
{
v_x_611_ = v_tail_614_;
goto _start;
}
else
{
lean_object* v___x_618_; 
lean_inc(v_head_613_);
v___x_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_618_, 0, v_head_613_);
return v___x_618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0___boxed(lean_object* v_backend_623_, lean_object* v_x_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_623_, v_x_624_);
lean_dec(v_x_624_);
lean_dec(v_backend_623_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux(lean_object* v_backend_626_, lean_object* v_entries_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_626_, v_entries_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux___boxed(lean_object* v_backend_629_, lean_object* v_entries_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_getExternEntryForAux(v_backend_629_, v_entries_630_);
lean_dec(v_entries_630_);
lean_dec(v_backend_629_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor(lean_object* v_d_632_, lean_object* v_backend_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_633_, v_d_632_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor___boxed(lean_object* v_d_635_, lean_object* v_backend_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_getExternEntryFor(v_d_635_, v_backend_636_);
lean_dec(v_backend_636_);
lean_dec(v_d_635_);
return v_res_637_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExtern(lean_object* v_env_638_, lean_object* v_fn_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_getExternAttrData_x3f(v_env_638_, v_fn_639_);
if (lean_obj_tag(v___x_640_) == 0)
{
uint8_t v___x_641_; 
v___x_641_ = 0;
return v___x_641_;
}
else
{
uint8_t v___x_642_; 
lean_dec_ref_known(v___x_640_, 1);
v___x_642_ = 1;
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExtern___boxed(lean_object* v_env_643_, lean_object* v_fn_644_){
_start:
{
uint8_t v_res_645_; lean_object* v_r_646_; 
v_res_645_ = l_Lean_isExtern(v_env_643_, v_fn_644_);
v_r_646_ = lean_box(v_res_645_);
return v_r_646_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExternC(lean_object* v_env_647_, lean_object* v_fn_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_getExternAttrData_x3f(v_env_647_, v_fn_648_);
if (lean_obj_tag(v___x_649_) == 1)
{
lean_object* v_val_650_; 
v_val_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_val_650_);
lean_dec_ref_known(v___x_649_, 1);
if (lean_obj_tag(v_val_650_) == 1)
{
lean_object* v_head_651_; 
v_head_651_ = lean_ctor_get(v_val_650_, 0);
if (lean_obj_tag(v_head_651_) == 2)
{
lean_object* v_backend_652_; 
v_backend_652_ = lean_ctor_get(v_head_651_, 0);
lean_inc(v_backend_652_);
if (lean_obj_tag(v_backend_652_) == 1)
{
lean_object* v_pre_653_; 
v_pre_653_ = lean_ctor_get(v_backend_652_, 0);
if (lean_obj_tag(v_pre_653_) == 0)
{
lean_object* v_tail_654_; lean_object* v_str_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_tail_654_ = lean_ctor_get(v_val_650_, 1);
lean_inc(v_tail_654_);
lean_dec_ref_known(v_val_650_, 2);
v_str_655_ = lean_ctor_get(v_backend_652_, 1);
lean_inc_ref(v_str_655_);
lean_dec_ref_known(v_backend_652_, 2);
v___x_656_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__2));
v___x_657_ = lean_string_dec_eq(v_str_655_, v___x_656_);
lean_dec_ref(v_str_655_);
if (v___x_657_ == 0)
{
lean_dec(v_tail_654_);
return v___x_657_;
}
else
{
if (lean_obj_tag(v_tail_654_) == 0)
{
return v___x_657_;
}
else
{
uint8_t v___x_658_; 
lean_dec(v_tail_654_);
v___x_658_ = 0;
return v___x_658_;
}
}
}
else
{
uint8_t v___x_659_; 
lean_dec_ref_known(v_backend_652_, 2);
lean_dec_ref_known(v_val_650_, 2);
v___x_659_ = 0;
return v___x_659_;
}
}
else
{
uint8_t v___x_660_; 
lean_dec(v_backend_652_);
lean_dec_ref_known(v_val_650_, 2);
v___x_660_ = 0;
return v___x_660_;
}
}
else
{
uint8_t v___x_661_; 
lean_dec_ref_known(v_val_650_, 2);
v___x_661_ = 0;
return v___x_661_;
}
}
else
{
uint8_t v___x_662_; 
lean_dec(v_val_650_);
v___x_662_ = 0;
return v___x_662_;
}
}
else
{
uint8_t v___x_663_; 
lean_dec(v___x_649_);
v___x_663_ = 0;
return v___x_663_;
}
}
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
