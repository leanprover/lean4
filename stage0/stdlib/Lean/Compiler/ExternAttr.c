// Lean compiler output
// Module: Lean.Compiler.ExternAttr
// Imports: public import Lean.ProjFns public import Lean.Attributes
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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_intersperseTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
uint8_t l_Lean_Environment_isConstructor(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_Pos_remainingBytes(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_List_getD___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_string_hash(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_registerParametricAttribute___redArg(lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_instHashableExternEntry_hash___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_instHashableExternEntry_hash___closed__1;
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
lean_object* lean_add_extern(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addExtern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__1_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__3_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "externAttr"};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 152, 26, 79, 119, 188, 216, 230)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__5_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "extern"};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(146, 128, 231, 207, 24, 58, 115, 13)}};
static const lean_object* l_Lean_initFn___closed__6_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__7_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "builtin and foreign functions"};
static const lean_object* l_Lean_initFn___closed__7_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__7_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__8_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__7_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_initFn___closed__8_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__8_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__9_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_initFn___closed__9_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__9_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__10_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__8_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__9_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_initFn___closed__10_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__10_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_externAttr;
LEAN_EXPORT lean_object* l_Lean_getExternAttrData_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_expandExternPatternAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_expandExternPatternAux___closed__0 = (const lean_object*)&l_Lean_expandExternPatternAux___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_getExternEntryForAux___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isExtern(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isExtern___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isExternC(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isExternC___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternNameFor(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_t_8_);
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
lean_object* v___x_90_; uint64_t v___x_91_; 
v___x_90_ = lean_unsigned_to_nat(1723u);
v___x_91_ = lean_uint64_of_nat(v___x_90_);
return v___x_91_;
}
}
static uint64_t _init_l_Lean_instHashableExternEntry_hash___closed__1(void){
_start:
{
uint64_t v___x_92_; uint64_t v___x_93_; uint64_t v___x_94_; 
v___x_92_ = lean_uint64_once(&l_Lean_instHashableExternEntry_hash___closed__0, &l_Lean_instHashableExternEntry_hash___closed__0_once, _init_l_Lean_instHashableExternEntry_hash___closed__0);
v___x_93_ = 0ULL;
v___x_94_ = lean_uint64_mix_hash(v___x_93_, v___x_92_);
return v___x_94_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableExternEntry_hash(lean_object* v_x_95_){
_start:
{
switch(lean_obj_tag(v_x_95_))
{
case 0:
{
lean_object* v_backend_96_; uint64_t v___x_97_; 
v_backend_96_ = lean_ctor_get(v_x_95_, 0);
v___x_97_ = 0ULL;
if (lean_obj_tag(v_backend_96_) == 0)
{
uint64_t v___x_98_; 
v___x_98_ = lean_uint64_once(&l_Lean_instHashableExternEntry_hash___closed__1, &l_Lean_instHashableExternEntry_hash___closed__1_once, _init_l_Lean_instHashableExternEntry_hash___closed__1);
return v___x_98_;
}
else
{
uint64_t v_hash_99_; uint64_t v___x_100_; 
v_hash_99_ = lean_ctor_get_uint64(v_backend_96_, sizeof(void*)*2);
v___x_100_ = lean_uint64_mix_hash(v___x_97_, v_hash_99_);
return v___x_100_;
}
}
case 1:
{
lean_object* v_backend_101_; lean_object* v_pattern_102_; uint64_t v___x_103_; uint64_t v___y_105_; 
v_backend_101_ = lean_ctor_get(v_x_95_, 0);
v_pattern_102_ = lean_ctor_get(v_x_95_, 1);
v___x_103_ = 1ULL;
if (lean_obj_tag(v_backend_101_) == 0)
{
uint64_t v___x_109_; 
v___x_109_ = lean_uint64_once(&l_Lean_instHashableExternEntry_hash___closed__0, &l_Lean_instHashableExternEntry_hash___closed__0_once, _init_l_Lean_instHashableExternEntry_hash___closed__0);
v___y_105_ = v___x_109_;
goto v___jp_104_;
}
else
{
uint64_t v_hash_110_; 
v_hash_110_ = lean_ctor_get_uint64(v_backend_101_, sizeof(void*)*2);
v___y_105_ = v_hash_110_;
goto v___jp_104_;
}
v___jp_104_:
{
uint64_t v___x_106_; uint64_t v___x_107_; uint64_t v___x_108_; 
v___x_106_ = lean_uint64_mix_hash(v___x_103_, v___y_105_);
v___x_107_ = lean_string_hash(v_pattern_102_);
v___x_108_ = lean_uint64_mix_hash(v___x_106_, v___x_107_);
return v___x_108_;
}
}
case 2:
{
lean_object* v_backend_111_; lean_object* v_fn_112_; uint64_t v___x_113_; uint64_t v___y_115_; 
v_backend_111_ = lean_ctor_get(v_x_95_, 0);
v_fn_112_ = lean_ctor_get(v_x_95_, 1);
v___x_113_ = 2ULL;
if (lean_obj_tag(v_backend_111_) == 0)
{
uint64_t v___x_119_; 
v___x_119_ = lean_uint64_once(&l_Lean_instHashableExternEntry_hash___closed__0, &l_Lean_instHashableExternEntry_hash___closed__0_once, _init_l_Lean_instHashableExternEntry_hash___closed__0);
v___y_115_ = v___x_119_;
goto v___jp_114_;
}
else
{
uint64_t v_hash_120_; 
v_hash_120_ = lean_ctor_get_uint64(v_backend_111_, sizeof(void*)*2);
v___y_115_ = v_hash_120_;
goto v___jp_114_;
}
v___jp_114_:
{
uint64_t v___x_116_; uint64_t v___x_117_; uint64_t v___x_118_; 
v___x_116_ = lean_uint64_mix_hash(v___x_113_, v___y_115_);
v___x_117_ = lean_string_hash(v_fn_112_);
v___x_118_ = lean_uint64_mix_hash(v___x_116_, v___x_117_);
return v___x_118_;
}
}
default: 
{
uint64_t v___x_121_; 
v___x_121_ = 3ULL;
return v___x_121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableExternEntry_hash___boxed(lean_object* v_x_122_){
_start:
{
uint64_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Lean_instHashableExternEntry_hash(v_x_122_);
lean_dec(v_x_122_);
v_r_124_ = lean_box_uint64(v_res_123_);
return v_r_124_;
}
}
static lean_object* _init_l_Lean_instInhabitedExternAttrData_default(void){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lean_box(0);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_instInhabitedExternAttrData(void){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lean_box(0);
return v___x_128_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0(lean_object* v_x_129_, lean_object* v_x_130_){
_start:
{
if (lean_obj_tag(v_x_129_) == 0)
{
if (lean_obj_tag(v_x_130_) == 0)
{
uint8_t v___x_131_; 
v___x_131_ = 1;
return v___x_131_;
}
else
{
uint8_t v___x_132_; 
v___x_132_ = 0;
return v___x_132_;
}
}
else
{
if (lean_obj_tag(v_x_130_) == 0)
{
uint8_t v___x_133_; 
v___x_133_ = 0;
return v___x_133_;
}
else
{
lean_object* v_head_134_; lean_object* v_tail_135_; lean_object* v_head_136_; lean_object* v_tail_137_; uint8_t v___x_138_; 
v_head_134_ = lean_ctor_get(v_x_129_, 0);
v_tail_135_ = lean_ctor_get(v_x_129_, 1);
v_head_136_ = lean_ctor_get(v_x_130_, 0);
v_tail_137_ = lean_ctor_get(v_x_130_, 1);
v___x_138_ = l_Lean_instBEqExternEntry_beq(v_head_134_, v_head_136_);
if (v___x_138_ == 0)
{
return v___x_138_;
}
else
{
v_x_129_ = v_tail_135_;
v_x_130_ = v_tail_137_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0___boxed(lean_object* v_x_140_, lean_object* v_x_141_){
_start:
{
uint8_t v_res_142_; lean_object* v_r_143_; 
v_res_142_ = l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0(v_x_140_, v_x_141_);
lean_dec(v_x_141_);
lean_dec(v_x_140_);
v_r_143_ = lean_box(v_res_142_);
return v_r_143_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqExternAttrData_beq(lean_object* v_x_144_, lean_object* v_x_145_){
_start:
{
uint8_t v___x_146_; 
v___x_146_ = l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0(v_x_144_, v_x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqExternAttrData_beq___boxed(lean_object* v_x_147_, lean_object* v_x_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l_Lean_instBEqExternAttrData_beq(v_x_147_, v_x_148_);
lean_dec(v_x_148_);
lean_dec(v_x_147_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0(uint64_t v_x_153_, lean_object* v_x_154_){
_start:
{
if (lean_obj_tag(v_x_154_) == 0)
{
return v_x_153_;
}
else
{
lean_object* v_head_155_; lean_object* v_tail_156_; uint64_t v___x_157_; uint64_t v___x_158_; 
v_head_155_ = lean_ctor_get(v_x_154_, 0);
v_tail_156_ = lean_ctor_get(v_x_154_, 1);
v___x_157_ = l_Lean_instHashableExternEntry_hash(v_head_155_);
v___x_158_ = lean_uint64_mix_hash(v_x_153_, v___x_157_);
v_x_153_ = v___x_158_;
v_x_154_ = v_tail_156_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0___boxed(lean_object* v_x_160_, lean_object* v_x_161_){
_start:
{
uint64_t v_x_57__boxed_162_; uint64_t v_res_163_; lean_object* v_r_164_; 
v_x_57__boxed_162_ = lean_unbox_uint64(v_x_160_);
lean_dec_ref(v_x_160_);
v_res_163_ = l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0(v_x_57__boxed_162_, v_x_161_);
lean_dec(v_x_161_);
v_r_164_ = lean_box_uint64(v_res_163_);
return v_r_164_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableExternAttrData_hash(lean_object* v_x_165_){
_start:
{
uint64_t v___x_166_; uint64_t v___x_167_; uint64_t v___x_168_; uint64_t v___x_169_; 
v___x_166_ = 0ULL;
v___x_167_ = 7ULL;
v___x_168_ = l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0(v___x_167_, v_x_165_);
v___x_169_ = lean_uint64_mix_hash(v___x_166_, v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableExternAttrData_hash___boxed(lean_object* v_x_170_){
_start:
{
uint64_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_Lean_instHashableExternAttrData_hash(v_x_170_);
lean_dec(v_x_170_);
v_r_172_ = lean_box_uint64(v_res_171_);
return v_r_172_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_175_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__0);
v___x_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1);
v___x_179_ = lean_unsigned_to_nat(0u);
v___x_180_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
lean_ctor_set(v___x_180_, 2, v___x_179_);
lean_ctor_set(v___x_180_, 3, v___x_178_);
lean_ctor_set(v___x_180_, 4, v___x_178_);
lean_ctor_set(v___x_180_, 5, v___x_178_);
lean_ctor_set(v___x_180_, 6, v___x_178_);
lean_ctor_set(v___x_180_, 7, v___x_178_);
lean_ctor_set(v___x_180_, 8, v___x_178_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = lean_unsigned_to_nat(32u);
v___x_182_ = lean_mk_empty_array_with_capacity(v___x_181_);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_184_ = ((size_t)5ULL);
v___x_185_ = lean_unsigned_to_nat(0u);
v___x_186_ = lean_unsigned_to_nat(32u);
v___x_187_ = lean_mk_empty_array_with_capacity(v___x_186_);
v___x_188_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3);
v___x_189_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v___x_187_);
lean_ctor_set(v___x_189_, 2, v___x_185_);
lean_ctor_set(v___x_189_, 3, v___x_185_);
lean_ctor_set_usize(v___x_189_, 4, v___x_184_);
return v___x_189_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_190_ = lean_box(1);
v___x_191_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4);
v___x_192_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1);
v___x_193_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v___x_191_);
lean_ctor_set(v___x_193_, 2, v___x_190_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1(lean_object* v_msgData_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v___x_198_; lean_object* v_env_199_; lean_object* v_options_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_198_ = lean_st_ref_get(v___y_196_);
v_env_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc_ref(v_env_199_);
lean_dec(v___x_198_);
v_options_200_ = lean_ctor_get(v___y_195_, 2);
v___x_201_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2);
v___x_202_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_200_);
v___x_203_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_203_, 0, v_env_199_);
lean_ctor_set(v___x_203_, 1, v___x_201_);
lean_ctor_set(v___x_203_, 2, v___x_202_);
lean_ctor_set(v___x_203_, 3, v_options_200_);
v___x_204_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v_msgData_194_);
v___x_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1(v_msgData_206_, v___y_207_, v___y_208_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(lean_object* v_msg_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_ref_215_; lean_object* v___x_216_; lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_225_; 
v_ref_215_ = lean_ctor_get(v___y_212_, 5);
v___x_216_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1(v_msg_211_, v___y_212_, v___y_213_);
v_a_217_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_225_ == 0)
{
v___x_219_ = v___x_216_;
v_isShared_220_ = v_isSharedCheck_225_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_225_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_221_; lean_object* v___x_223_; 
lean_inc(v_ref_215_);
v___x_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_221_, 0, v_ref_215_);
lean_ctor_set(v___x_221_, 1, v_a_217_);
if (v_isShared_220_ == 0)
{
lean_ctor_set_tag(v___x_219_, 1);
lean_ctor_set(v___x_219_, 0, v___x_221_);
v___x_223_ = v___x_219_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg___boxed(lean_object* v_msg_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_226_, v___y_227_, v___y_228_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(lean_object* v_ref_231_, lean_object* v_msg_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v_fileName_236_; lean_object* v_fileMap_237_; lean_object* v_options_238_; lean_object* v_currRecDepth_239_; lean_object* v_maxRecDepth_240_; lean_object* v_ref_241_; lean_object* v_currNamespace_242_; lean_object* v_openDecls_243_; lean_object* v_initHeartbeats_244_; lean_object* v_maxHeartbeats_245_; lean_object* v_quotContext_246_; lean_object* v_currMacroScope_247_; uint8_t v_diag_248_; lean_object* v_cancelTk_x3f_249_; uint8_t v_suppressElabErrors_250_; lean_object* v_inheritedTraceOptions_251_; lean_object* v_ref_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_fileName_236_ = lean_ctor_get(v___y_233_, 0);
v_fileMap_237_ = lean_ctor_get(v___y_233_, 1);
v_options_238_ = lean_ctor_get(v___y_233_, 2);
v_currRecDepth_239_ = lean_ctor_get(v___y_233_, 3);
v_maxRecDepth_240_ = lean_ctor_get(v___y_233_, 4);
v_ref_241_ = lean_ctor_get(v___y_233_, 5);
v_currNamespace_242_ = lean_ctor_get(v___y_233_, 6);
v_openDecls_243_ = lean_ctor_get(v___y_233_, 7);
v_initHeartbeats_244_ = lean_ctor_get(v___y_233_, 8);
v_maxHeartbeats_245_ = lean_ctor_get(v___y_233_, 9);
v_quotContext_246_ = lean_ctor_get(v___y_233_, 10);
v_currMacroScope_247_ = lean_ctor_get(v___y_233_, 11);
v_diag_248_ = lean_ctor_get_uint8(v___y_233_, sizeof(void*)*14);
v_cancelTk_x3f_249_ = lean_ctor_get(v___y_233_, 12);
v_suppressElabErrors_250_ = lean_ctor_get_uint8(v___y_233_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_251_ = lean_ctor_get(v___y_233_, 13);
v_ref_252_ = l_Lean_replaceRef(v_ref_231_, v_ref_241_);
lean_inc_ref(v_inheritedTraceOptions_251_);
lean_inc(v_cancelTk_x3f_249_);
lean_inc(v_currMacroScope_247_);
lean_inc(v_quotContext_246_);
lean_inc(v_maxHeartbeats_245_);
lean_inc(v_initHeartbeats_244_);
lean_inc(v_openDecls_243_);
lean_inc(v_currNamespace_242_);
lean_inc(v_maxRecDepth_240_);
lean_inc(v_currRecDepth_239_);
lean_inc_ref(v_options_238_);
lean_inc_ref(v_fileMap_237_);
lean_inc_ref(v_fileName_236_);
v___x_253_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_253_, 0, v_fileName_236_);
lean_ctor_set(v___x_253_, 1, v_fileMap_237_);
lean_ctor_set(v___x_253_, 2, v_options_238_);
lean_ctor_set(v___x_253_, 3, v_currRecDepth_239_);
lean_ctor_set(v___x_253_, 4, v_maxRecDepth_240_);
lean_ctor_set(v___x_253_, 5, v_ref_252_);
lean_ctor_set(v___x_253_, 6, v_currNamespace_242_);
lean_ctor_set(v___x_253_, 7, v_openDecls_243_);
lean_ctor_set(v___x_253_, 8, v_initHeartbeats_244_);
lean_ctor_set(v___x_253_, 9, v_maxHeartbeats_245_);
lean_ctor_set(v___x_253_, 10, v_quotContext_246_);
lean_ctor_set(v___x_253_, 11, v_currMacroScope_247_);
lean_ctor_set(v___x_253_, 12, v_cancelTk_x3f_249_);
lean_ctor_set(v___x_253_, 13, v_inheritedTraceOptions_251_);
lean_ctor_set_uint8(v___x_253_, sizeof(void*)*14, v_diag_248_);
lean_ctor_set_uint8(v___x_253_, sizeof(void*)*14 + 1, v_suppressElabErrors_250_);
v___x_254_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_232_, v___x_253_, v___y_234_);
lean_dec_ref(v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg___boxed(lean_object* v_ref_255_, lean_object* v_msg_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v_ref_255_, v_msg_256_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v_ref_255_);
return v_res_260_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__0));
v___x_263_ = l_Lean_stringToMessageData(v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(lean_object* v_as_267_, size_t v_sz_268_, size_t v_i_269_, lean_object* v_b_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_a_275_; uint8_t v___x_279_; 
v___x_279_ = lean_usize_dec_lt(v_i_269_, v_sz_268_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; 
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v_b_270_);
return v___x_280_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v_a_283_; lean_object* v___y_285_; lean_object* v_str_286_; lean_object* v___y_294_; lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_281_ = lean_unsigned_to_nat(1u);
v___x_282_ = lean_unsigned_to_nat(0u);
v_a_283_ = lean_array_uget_borrowed(v_as_267_, v_i_269_);
v___x_310_ = l_Lean_Syntax_getArg(v_a_283_, v___x_282_);
v___x_311_ = l_Lean_Syntax_isNone(v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = l_Lean_Syntax_getArg(v___x_310_, v___x_282_);
lean_dec(v___x_310_);
v___x_313_ = l_Lean_Syntax_getId(v___x_312_);
lean_dec(v___x_312_);
v___y_294_ = v___x_313_;
goto v___jp_293_;
}
else
{
lean_object* v___x_314_; 
lean_dec(v___x_310_);
v___x_314_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
v___y_294_ = v___x_314_;
goto v___jp_293_;
}
v___jp_284_:
{
lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = l_Lean_Syntax_getArg(v_a_283_, v___x_281_);
v___x_288_ = l_Lean_Syntax_isNone(v___x_287_);
lean_dec(v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_289_, 0, v___y_285_);
lean_ctor_set(v___x_289_, 1, v_str_286_);
v___x_290_ = lean_array_push(v_b_270_, v___x_289_);
v_a_275_ = v___x_290_;
goto v___jp_274_;
}
else
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_291_, 0, v___y_285_);
lean_ctor_set(v___x_291_, 1, v_str_286_);
v___x_292_ = lean_array_push(v_b_270_, v___x_291_);
v_a_275_ = v___x_292_;
goto v___jp_274_;
}
}
v___jp_293_:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = lean_unsigned_to_nat(2u);
v___x_296_ = l_Lean_Syntax_getArg(v_a_283_, v___x_295_);
v___x_297_ = l_Lean_Syntax_isStrLit_x3f(v___x_296_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1);
v___x_299_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v___x_296_, v___x_298_, v___y_271_, v___y_272_);
lean_dec(v___x_296_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_300_);
lean_dec_ref(v___x_299_);
v___y_285_ = v___y_294_;
v_str_286_ = v_a_300_;
goto v___jp_284_;
}
else
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
lean_dec(v___y_294_);
lean_dec_ref(v_b_270_);
v_a_301_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_299_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_299_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
else
{
lean_object* v_val_309_; 
lean_dec(v___x_296_);
v_val_309_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_val_309_);
lean_dec_ref(v___x_297_);
v___y_285_ = v___y_294_;
v_str_286_ = v_val_309_;
goto v___jp_284_;
}
}
}
v___jp_274_:
{
size_t v___x_276_; size_t v___x_277_; 
v___x_276_ = ((size_t)1ULL);
v___x_277_ = lean_usize_add(v_i_269_, v___x_276_);
v_i_269_ = v___x_277_;
v_b_270_ = v_a_275_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___boxed(lean_object* v_as_315_, lean_object* v_sz_316_, lean_object* v_i_317_, lean_object* v_b_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
size_t v_sz_boxed_322_; size_t v_i_boxed_323_; lean_object* v_res_324_; 
v_sz_boxed_322_ = lean_unbox_usize(v_sz_316_);
lean_dec(v_sz_316_);
v_i_boxed_323_ = lean_unbox_usize(v_i_317_);
lean_dec(v_i_317_);
v_res_324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(v_as_315_, v_sz_boxed_322_, v_i_boxed_323_, v_b_318_, v___y_319_, v___y_320_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec_ref(v_as_315_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(lean_object* v_stx_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v_entriesStx_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = l_Lean_Syntax_getArg(v_stx_332_, v___x_336_);
v_entriesStx_338_ = l_Lean_Syntax_getArgs(v___x_337_);
lean_dec(v___x_337_);
v___x_339_ = lean_array_get_size(v_entriesStx_338_);
v___x_340_ = lean_unsigned_to_nat(0u);
v___x_341_ = lean_nat_dec_eq(v___x_339_, v___x_340_);
if (v___x_341_ == 0)
{
lean_object* v_entries_342_; size_t v_sz_343_; size_t v___x_344_; lean_object* v___x_345_; 
v_entries_342_ = ((lean_object*)(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__0));
v_sz_343_ = lean_array_size(v_entriesStx_338_);
v___x_344_ = ((size_t)0ULL);
v___x_345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(v_entriesStx_338_, v_sz_343_, v___x_344_, v_entries_342_, v_a_333_, v_a_334_);
lean_dec_ref(v_entriesStx_338_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_354_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_354_ == 0)
{
v___x_348_ = v___x_345_;
v_isShared_349_ = v_isSharedCheck_354_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_354_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_350_ = lean_array_to_list(v_a_346_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_350_);
v___x_352_ = v___x_348_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
v_a_355_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_345_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_345_);
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
else
{
lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec_ref(v_entriesStx_338_);
v___x_363_ = ((lean_object*)(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2));
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___boxed(lean_object* v_stx_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(v_stx_365_, v_a_366_, v_a_367_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_stx_365_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(lean_object* v_00_u03b1_370_, lean_object* v_ref_371_, lean_object* v_msg_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v_ref_371_, v_msg_372_, v___y_373_, v___y_374_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___boxed(lean_object* v_00_u03b1_377_, lean_object* v_ref_378_, lean_object* v_msg_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(v_00_u03b1_377_, v_ref_378_, v_msg_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v_ref_378_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0(lean_object* v_00_u03b1_384_, lean_object* v_msg_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_385_, v___y_386_, v___y_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___boxed(lean_object* v_00_u03b1_390_, lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0(v_00_u03b1_390_, v_msg_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_addExtern___boxed(lean_object* v_declName_401_, lean_object* v_externAttrData_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_00___x40___internal___hyg_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = lean_add_extern(v_declName_401_, v_externAttrData_402_, v_a_403_, v_a_404_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_(lean_object* v_x_407_, lean_object* v_stx_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(v_stx_408_, v___y_409_, v___y_410_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2____boxed(lean_object* v_x_413_, lean_object* v_stx_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_(v_x_413_, v_stx_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v_stx_414_);
lean_dec(v_x_413_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_(lean_object* v_declName_419_, lean_object* v_externAttrData_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v___x_424_; lean_object* v_env_425_; uint8_t v___y_427_; uint8_t v___x_444_; 
v___x_424_ = lean_st_ref_get(v___y_422_);
v_env_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc_ref(v_env_425_);
lean_dec(v___x_424_);
lean_inc(v_declName_419_);
lean_inc_ref(v_env_425_);
v___x_444_ = l_Lean_Environment_isProjectionFn(v_env_425_, v_declName_419_);
if (v___x_444_ == 0)
{
uint8_t v___x_445_; 
lean_inc(v_declName_419_);
lean_inc_ref(v_env_425_);
v___x_445_ = l_Lean_Environment_isConstructor(v_env_425_, v_declName_419_);
v___y_427_ = v___x_445_;
goto v___jp_426_;
}
else
{
v___y_427_ = v___x_444_;
goto v___jp_426_;
}
v___jp_426_:
{
if (v___y_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; 
lean_dec_ref(v_env_425_);
lean_dec(v_externAttrData_420_);
lean_dec(v_declName_419_);
v___x_428_ = lean_box(0);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
else
{
uint8_t v___x_430_; lean_object* v___x_431_; 
v___x_430_ = 0;
lean_inc(v_declName_419_);
v___x_431_ = l_Lean_Environment_find_x3f(v_env_425_, v_declName_419_, v___x_430_);
if (lean_obj_tag(v___x_431_) == 1)
{
lean_object* v_val_432_; 
v_val_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_val_432_);
lean_dec_ref(v___x_431_);
if (lean_obj_tag(v_val_432_) == 2)
{
lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_440_; 
lean_dec(v_externAttrData_420_);
lean_dec(v_declName_419_);
v_isSharedCheck_440_ = !lean_is_exclusive(v_val_432_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; 
v_unused_441_ = lean_ctor_get(v_val_432_, 0);
lean_dec(v_unused_441_);
v___x_434_ = v_val_432_;
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
else
{
lean_dec(v_val_432_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = lean_box(0);
if (v_isShared_435_ == 0)
{
lean_ctor_set_tag(v___x_434_, 0);
lean_ctor_set(v___x_434_, 0, v___x_436_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
else
{
lean_object* v___x_442_; 
lean_dec(v_val_432_);
lean_inc(v___y_422_);
lean_inc_ref(v___y_421_);
v___x_442_ = lean_add_extern(v_declName_419_, v_externAttrData_420_, v___y_421_, v___y_422_);
return v___x_442_;
}
}
else
{
lean_object* v___x_443_; 
lean_dec(v___x_431_);
lean_inc(v___y_422_);
lean_inc_ref(v___y_421_);
v___x_443_ = lean_add_extern(v_declName_419_, v_externAttrData_420_, v___y_421_, v___y_422_);
return v___x_443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2____boxed(lean_object* v_declName_446_, lean_object* v_externAttrData_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_(v_declName_446_, v_externAttrData_447_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
return v_res_451_;
}
}
LEAN_EXPORT uint8_t l_Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_(uint8_t v___x_452_, lean_object* v_env_453_, lean_object* v_n_454_, lean_object* v_x_455_){
_start:
{
uint8_t v___x_456_; 
v___x_456_ = l_Lean_Environment_contains(v_env_453_, v_n_454_, v___x_452_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2____boxed(lean_object* v___x_457_, lean_object* v_env_458_, lean_object* v_n_459_, lean_object* v_x_460_){
_start:
{
uint8_t v___x_600__boxed_461_; uint8_t v_res_462_; lean_object* v_r_463_; 
v___x_600__boxed_461_ = lean_unbox(v___x_457_);
v_res_462_ = l_Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_(v___x_600__boxed_461_, v_env_458_, v_n_459_, v_x_460_);
lean_dec(v_x_460_);
v_r_463_ = lean_box(v_res_462_);
return v_r_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = ((lean_object*)(l_Lean_initFn___closed__10_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_));
v___x_491_ = l_Lean_registerParametricAttribute___redArg(v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2____boxed(lean_object* v_a_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_initFn_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_();
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternAttrData_x3f(lean_object* v_env_494_, lean_object* v_n_495_){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_496_ = lean_box(0);
v___x_497_ = l_Lean_externAttr;
v___x_498_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_496_, v___x_497_, v_env_494_, v_n_495_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(lean_object* v_x_499_, lean_object* v_x_500_, lean_object* v_x_501_, lean_object* v_x_502_){
_start:
{
lean_object* v_zero_503_; uint8_t v_isZero_504_; 
v_zero_503_ = lean_unsigned_to_nat(0u);
v_isZero_504_ = lean_nat_dec_eq(v_x_499_, v_zero_503_);
if (v_isZero_504_ == 1)
{
lean_object* v___x_505_; 
lean_dec(v_x_499_);
v___x_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_505_, 0, v_x_501_);
lean_ctor_set(v___x_505_, 1, v_x_502_);
return v___x_505_;
}
else
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = lean_string_utf8_byte_size(v_x_500_);
v___x_507_ = lean_nat_dec_eq(v_x_501_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v_one_508_; lean_object* v_n_509_; uint32_t v_c_510_; uint8_t v___y_512_; uint32_t v___x_522_; uint8_t v___x_523_; 
v_one_508_ = lean_unsigned_to_nat(1u);
v_n_509_ = lean_nat_sub(v_x_499_, v_one_508_);
lean_dec(v_x_499_);
v_c_510_ = lean_string_utf8_get_fast(v_x_500_, v_x_501_);
v___x_522_ = 48;
v___x_523_ = lean_uint32_dec_le(v___x_522_, v_c_510_);
if (v___x_523_ == 0)
{
v___y_512_ = v___x_523_;
goto v___jp_511_;
}
else
{
uint32_t v___x_524_; uint8_t v___x_525_; 
v___x_524_ = 57;
v___x_525_ = lean_uint32_dec_le(v_c_510_, v___x_524_);
v___y_512_ = v___x_525_;
goto v___jp_511_;
}
v___jp_511_:
{
if (v___y_512_ == 0)
{
lean_object* v___x_513_; 
lean_dec(v_n_509_);
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v_x_501_);
lean_ctor_set(v___x_513_, 1, v_x_502_);
return v___x_513_;
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_514_ = lean_string_utf8_next_fast(v_x_500_, v_x_501_);
lean_dec(v_x_501_);
v___x_515_ = lean_unsigned_to_nat(10u);
v___x_516_ = lean_nat_mul(v_x_502_, v___x_515_);
lean_dec(v_x_502_);
v___x_517_ = lean_uint32_to_nat(v_c_510_);
v___x_518_ = lean_unsigned_to_nat(48u);
v___x_519_ = lean_nat_sub(v___x_517_, v___x_518_);
lean_dec(v___x_517_);
v___x_520_ = lean_nat_add(v___x_516_, v___x_519_);
lean_dec(v___x_519_);
lean_dec(v___x_516_);
v_x_499_ = v_n_509_;
v_x_501_ = v___x_514_;
v_x_502_ = v___x_520_;
goto _start;
}
}
}
else
{
lean_object* v___x_526_; 
lean_dec(v_x_499_);
v___x_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_526_, 0, v_x_501_);
lean_ctor_set(v___x_526_, 1, v_x_502_);
return v___x_526_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum___boxed(lean_object* v_x_527_, lean_object* v_x_528_, lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(v_x_527_, v_x_528_, v_x_529_, v_x_530_);
lean_dec_ref(v_x_528_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux(lean_object* v_args_533_, lean_object* v_x_534_, lean_object* v_x_535_, lean_object* v_x_536_, lean_object* v_x_537_){
_start:
{
lean_object* v_zero_538_; uint8_t v_isZero_539_; 
v_zero_538_ = lean_unsigned_to_nat(0u);
v_isZero_539_ = lean_nat_dec_eq(v_x_534_, v_zero_538_);
if (v_isZero_539_ == 1)
{
lean_dec(v_x_536_);
lean_dec_ref(v_x_535_);
lean_dec(v_x_534_);
return v_x_537_;
}
else
{
lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_540_ = lean_string_utf8_byte_size(v_x_535_);
v___x_541_ = lean_nat_dec_eq(v_x_536_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v_one_542_; lean_object* v_n_543_; uint32_t v_c_544_; uint32_t v___x_549_; uint8_t v___x_550_; 
v_one_542_ = lean_unsigned_to_nat(1u);
v_n_543_ = lean_nat_sub(v_x_534_, v_one_542_);
lean_dec(v_x_534_);
v_c_544_ = lean_string_utf8_get_fast(v_x_535_, v_x_536_);
v___x_549_ = 35;
v___x_550_ = lean_uint32_dec_eq(v_c_544_, v___x_549_);
if (v___x_550_ == 0)
{
goto v___jp_545_;
}
else
{
if (v___x_541_ == 0)
{
lean_object* v_it_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v_fst_554_; lean_object* v_snd_555_; lean_object* v_j_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v_it_551_ = lean_string_utf8_next_fast(v_x_535_, v_x_536_);
lean_dec(v_x_536_);
lean_inc_ref(v_x_535_);
v___x_552_ = l_String_Pos_remainingBytes(v_x_535_, v_it_551_);
v___x_553_ = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(v___x_552_, v_x_535_, v_it_551_, v_zero_538_);
v_fst_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_fst_554_);
v_snd_555_ = lean_ctor_get(v___x_553_, 1);
lean_inc(v_snd_555_);
lean_dec_ref(v___x_553_);
v_j_556_ = lean_nat_sub(v_snd_555_, v_one_542_);
lean_dec(v_snd_555_);
v___x_557_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_558_ = l_List_getD___redArg(v_args_533_, v_j_556_, v___x_557_);
v___x_559_ = lean_string_append(v_x_537_, v___x_558_);
lean_dec(v___x_558_);
v_x_534_ = v_n_543_;
v_x_536_ = v_fst_554_;
v_x_537_ = v___x_559_;
goto _start;
}
else
{
goto v___jp_545_;
}
}
v___jp_545_:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_string_utf8_next_fast(v_x_535_, v_x_536_);
lean_dec(v_x_536_);
v___x_547_ = lean_string_push(v_x_537_, v_c_544_);
v_x_534_ = v_n_543_;
v_x_536_ = v___x_546_;
v_x_537_ = v___x_547_;
goto _start;
}
}
else
{
lean_dec(v_x_536_);
lean_dec_ref(v_x_535_);
lean_dec(v_x_534_);
return v_x_537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux___boxed(lean_object* v_args_561_, lean_object* v_x_562_, lean_object* v_x_563_, lean_object* v_x_564_, lean_object* v_x_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_expandExternPatternAux(v_args_561_, v_x_562_, v_x_563_, v_x_564_, v_x_565_);
lean_dec(v_args_561_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPattern(lean_object* v_pattern_567_, lean_object* v_args_568_){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_569_ = lean_string_length(v_pattern_567_);
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_572_ = l_Lean_expandExternPatternAux(v_args_568_, v___x_569_, v_pattern_567_, v___x_570_, v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPattern___boxed(lean_object* v_pattern_573_, lean_object* v_args_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_expandExternPattern(v_pattern_573_, v_args_574_);
lean_dec(v_args_574_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(lean_object* v_x_576_, lean_object* v_x_577_){
_start:
{
if (lean_obj_tag(v_x_577_) == 0)
{
return v_x_576_;
}
else
{
lean_object* v_head_578_; lean_object* v_tail_579_; lean_object* v___x_580_; 
v_head_578_ = lean_ctor_get(v_x_577_, 0);
v_tail_579_ = lean_ctor_get(v_x_577_, 1);
v___x_580_ = lean_string_append(v_x_576_, v_head_578_);
v_x_576_ = v___x_580_;
v_x_577_ = v_tail_579_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0___boxed(lean_object* v_x_582_, lean_object* v_x_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(v_x_582_, v_x_583_);
lean_dec(v_x_583_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleFnCall(lean_object* v_fn_588_, lean_object* v_args_589_){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_590_ = ((lean_object*)(l_Lean_mkSimpleFnCall___closed__0));
v___x_591_ = lean_string_append(v_fn_588_, v___x_590_);
v___x_592_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_593_ = ((lean_object*)(l_Lean_mkSimpleFnCall___closed__1));
v___x_594_ = l_List_intersperseTR___redArg(v___x_593_, v_args_589_);
v___x_595_ = l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(v___x_592_, v___x_594_);
lean_dec(v___x_594_);
v___x_596_ = lean_string_append(v___x_591_, v___x_595_);
lean_dec_ref(v___x_595_);
v___x_597_ = ((lean_object*)(l_Lean_mkSimpleFnCall___closed__2));
v___x_598_ = lean_string_append(v___x_596_, v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend(lean_object* v_x_599_){
_start:
{
if (lean_obj_tag(v_x_599_) == 3)
{
lean_object* v___x_600_; 
v___x_600_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
return v___x_600_;
}
else
{
lean_object* v_backend_601_; 
v_backend_601_ = lean_ctor_get(v_x_599_, 0);
lean_inc(v_backend_601_);
return v_backend_601_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend___boxed(lean_object* v_x_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_ExternEntry_backend(v_x_602_);
lean_dec(v_x_602_);
return v_res_603_;
}
}
LEAN_EXPORT uint8_t l_Lean_getExternEntryForAux___lam__0(lean_object* v_backend_604_, lean_object* v_e_605_){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_606_ = l_Lean_ExternEntry_backend(v_e_605_);
v___x_607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
v___x_608_ = lean_name_eq(v___x_606_, v___x_607_);
if (v___x_608_ == 0)
{
uint8_t v___x_609_; 
v___x_609_ = lean_name_eq(v___x_606_, v_backend_604_);
lean_dec(v___x_606_);
return v___x_609_;
}
else
{
lean_dec(v___x_606_);
return v___x_608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux___lam__0___boxed(lean_object* v_backend_610_, lean_object* v_e_611_){
_start:
{
uint8_t v_res_612_; lean_object* v_r_613_; 
v_res_612_ = l_Lean_getExternEntryForAux___lam__0(v_backend_610_, v_e_611_);
lean_dec(v_e_611_);
lean_dec(v_backend_610_);
v_r_613_ = lean_box(v_res_612_);
return v_r_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux(lean_object* v_backend_614_, lean_object* v_entries_615_){
_start:
{
lean_object* v___f_616_; lean_object* v___x_617_; 
v___f_616_ = lean_alloc_closure((void*)(l_Lean_getExternEntryForAux___lam__0___boxed), 2, 1);
lean_closure_set(v___f_616_, 0, v_backend_614_);
v___x_617_ = l_List_find_x3f___redArg(v___f_616_, v_entries_615_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor(lean_object* v_d_618_, lean_object* v_backend_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_getExternEntryForAux(v_backend_619_, v_d_618_);
return v___x_620_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExtern(lean_object* v_env_621_, lean_object* v_fn_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_getExternAttrData_x3f(v_env_621_, v_fn_622_);
if (lean_obj_tag(v___x_623_) == 0)
{
uint8_t v___x_624_; 
v___x_624_ = 0;
return v___x_624_;
}
else
{
uint8_t v___x_625_; 
lean_dec_ref(v___x_623_);
v___x_625_ = 1;
return v___x_625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExtern___boxed(lean_object* v_env_626_, lean_object* v_fn_627_){
_start:
{
uint8_t v_res_628_; lean_object* v_r_629_; 
v_res_628_ = l_Lean_isExtern(v_env_626_, v_fn_627_);
v_r_629_ = lean_box(v_res_628_);
return v_r_629_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExternC(lean_object* v_env_630_, lean_object* v_fn_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_getExternAttrData_x3f(v_env_630_, v_fn_631_);
if (lean_obj_tag(v___x_632_) == 1)
{
lean_object* v_val_633_; 
v_val_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_val_633_);
lean_dec_ref(v___x_632_);
if (lean_obj_tag(v_val_633_) == 1)
{
lean_object* v_head_634_; 
v_head_634_ = lean_ctor_get(v_val_633_, 0);
if (lean_obj_tag(v_head_634_) == 2)
{
lean_object* v_backend_635_; 
v_backend_635_ = lean_ctor_get(v_head_634_, 0);
lean_inc(v_backend_635_);
if (lean_obj_tag(v_backend_635_) == 1)
{
lean_object* v_pre_636_; 
v_pre_636_ = lean_ctor_get(v_backend_635_, 0);
if (lean_obj_tag(v_pre_636_) == 0)
{
lean_object* v_tail_637_; lean_object* v_str_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v_tail_637_ = lean_ctor_get(v_val_633_, 1);
lean_inc(v_tail_637_);
lean_dec_ref(v_val_633_);
v_str_638_ = lean_ctor_get(v_backend_635_, 1);
lean_inc_ref(v_str_638_);
lean_dec_ref(v_backend_635_);
v___x_639_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__2));
v___x_640_ = lean_string_dec_eq(v_str_638_, v___x_639_);
lean_dec_ref(v_str_638_);
if (v___x_640_ == 0)
{
lean_dec(v_tail_637_);
return v___x_640_;
}
else
{
if (lean_obj_tag(v_tail_637_) == 0)
{
return v___x_640_;
}
else
{
uint8_t v___x_641_; 
lean_dec(v_tail_637_);
v___x_641_ = 0;
return v___x_641_;
}
}
}
else
{
uint8_t v___x_642_; 
lean_dec_ref(v_backend_635_);
lean_dec_ref(v_val_633_);
v___x_642_ = 0;
return v___x_642_;
}
}
else
{
uint8_t v___x_643_; 
lean_dec(v_backend_635_);
lean_dec_ref(v_val_633_);
v___x_643_ = 0;
return v___x_643_;
}
}
else
{
uint8_t v___x_644_; 
lean_dec_ref(v_val_633_);
v___x_644_ = 0;
return v___x_644_;
}
}
else
{
uint8_t v___x_645_; 
lean_dec(v_val_633_);
v___x_645_ = 0;
return v___x_645_;
}
}
else
{
uint8_t v___x_646_; 
lean_dec(v___x_632_);
v___x_646_ = 0;
return v___x_646_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExternC___boxed(lean_object* v_env_647_, lean_object* v_fn_648_){
_start:
{
uint8_t v_res_649_; lean_object* v_r_650_; 
v_res_649_ = l_Lean_isExternC(v_env_647_, v_fn_648_);
v_r_650_ = lean_box(v_res_649_);
return v_r_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternNameFor(lean_object* v_env_651_, lean_object* v_backend_652_, lean_object* v_fn_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_getExternAttrData_x3f(v_env_651_, v_fn_653_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v___x_655_; 
lean_dec(v_backend_652_);
v___x_655_ = lean_box(0);
return v___x_655_;
}
else
{
lean_object* v_val_656_; lean_object* v___x_657_; 
v_val_656_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_val_656_);
lean_dec_ref(v___x_654_);
v___x_657_ = l_Lean_getExternEntryForAux(v_backend_652_, v_val_656_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v___x_658_; 
v___x_658_ = lean_box(0);
return v___x_658_;
}
else
{
lean_object* v_val_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_668_; 
v_val_659_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_668_ == 0)
{
v___x_661_ = v___x_657_;
v_isShared_662_ = v_isSharedCheck_668_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_val_659_);
lean_dec(v___x_657_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_668_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
if (lean_obj_tag(v_val_659_) == 2)
{
lean_object* v_fn_663_; lean_object* v___x_665_; 
v_fn_663_ = lean_ctor_get(v_val_659_, 1);
lean_inc_ref(v_fn_663_);
lean_dec_ref(v_val_659_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v_fn_663_);
v___x_665_ = v___x_661_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_fn_663_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
else
{
lean_object* v___x_667_; 
lean_del_object(v___x_661_);
lean_dec(v_val_659_);
v___x_667_ = lean_box(0);
return v___x_667_;
}
}
}
}
}
}
lean_object* runtime_initialize_Lean_ProjFns(uint8_t builtin);
lean_object* runtime_initialize_Lean_Attributes(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_ExternAttr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_ProjFns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedExternAttrData_default = _init_l_Lean_instInhabitedExternAttrData_default();
lean_mark_persistent(l_Lean_instInhabitedExternAttrData_default);
l_Lean_instInhabitedExternAttrData = _init_l_Lean_instInhabitedExternAttrData();
lean_mark_persistent(l_Lean_instInhabitedExternAttrData);
res = l_Lean_initFn_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_();
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
