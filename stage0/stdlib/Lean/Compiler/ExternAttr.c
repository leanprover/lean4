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
lean_object* v_fileName_236_; lean_object* v_fileMap_237_; lean_object* v_options_238_; lean_object* v_currRecDepth_239_; lean_object* v_maxRecDepth_240_; lean_object* v_ref_241_; lean_object* v_currNamespace_242_; lean_object* v_openDecls_243_; lean_object* v_initHeartbeats_244_; lean_object* v_maxHeartbeats_245_; lean_object* v_quotContext_246_; lean_object* v_currMacroScope_247_; uint8_t v_diag_248_; lean_object* v_cancelTk_x3f_249_; uint8_t v_suppressElabErrors_250_; lean_object* v_inheritedTraceOptions_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_260_; 
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
v_isSharedCheck_260_ = !lean_is_exclusive(v___y_233_);
if (v_isSharedCheck_260_ == 0)
{
v___x_253_ = v___y_233_;
v_isShared_254_ = v_isSharedCheck_260_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_inheritedTraceOptions_251_);
lean_inc(v_cancelTk_x3f_249_);
lean_inc(v_currMacroScope_247_);
lean_inc(v_quotContext_246_);
lean_inc(v_maxHeartbeats_245_);
lean_inc(v_initHeartbeats_244_);
lean_inc(v_openDecls_243_);
lean_inc(v_currNamespace_242_);
lean_inc(v_ref_241_);
lean_inc(v_maxRecDepth_240_);
lean_inc(v_currRecDepth_239_);
lean_inc(v_options_238_);
lean_inc(v_fileMap_237_);
lean_inc(v_fileName_236_);
lean_dec(v___y_233_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_260_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v_ref_255_; lean_object* v___x_257_; 
v_ref_255_ = l_Lean_replaceRef(v_ref_231_, v_ref_241_);
lean_dec(v_ref_241_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 5, v_ref_255_);
v___x_257_ = v___x_253_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_fileName_236_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_fileMap_237_);
lean_ctor_set(v_reuseFailAlloc_259_, 2, v_options_238_);
lean_ctor_set(v_reuseFailAlloc_259_, 3, v_currRecDepth_239_);
lean_ctor_set(v_reuseFailAlloc_259_, 4, v_maxRecDepth_240_);
lean_ctor_set(v_reuseFailAlloc_259_, 5, v_ref_255_);
lean_ctor_set(v_reuseFailAlloc_259_, 6, v_currNamespace_242_);
lean_ctor_set(v_reuseFailAlloc_259_, 7, v_openDecls_243_);
lean_ctor_set(v_reuseFailAlloc_259_, 8, v_initHeartbeats_244_);
lean_ctor_set(v_reuseFailAlloc_259_, 9, v_maxHeartbeats_245_);
lean_ctor_set(v_reuseFailAlloc_259_, 10, v_quotContext_246_);
lean_ctor_set(v_reuseFailAlloc_259_, 11, v_currMacroScope_247_);
lean_ctor_set(v_reuseFailAlloc_259_, 12, v_cancelTk_x3f_249_);
lean_ctor_set(v_reuseFailAlloc_259_, 13, v_inheritedTraceOptions_251_);
lean_ctor_set_uint8(v_reuseFailAlloc_259_, sizeof(void*)*14, v_diag_248_);
lean_ctor_set_uint8(v_reuseFailAlloc_259_, sizeof(void*)*14 + 1, v_suppressElabErrors_250_);
v___x_257_ = v_reuseFailAlloc_259_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_232_, v___x_257_, v___y_234_);
lean_dec_ref(v___x_257_);
return v___x_258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg___boxed(lean_object* v_ref_261_, lean_object* v_msg_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v_ref_261_, v_msg_262_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec(v_ref_261_);
return v_res_266_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__0));
v___x_269_ = l_Lean_stringToMessageData(v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(lean_object* v_as_273_, size_t v_sz_274_, size_t v_i_275_, lean_object* v_b_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_a_281_; uint8_t v___x_285_; 
v___x_285_ = lean_usize_dec_lt(v_i_275_, v_sz_274_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; 
lean_dec_ref(v___y_277_);
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v_b_276_);
return v___x_286_;
}
else
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v_a_289_; lean_object* v___y_291_; lean_object* v_str_292_; lean_object* v___y_300_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_287_ = lean_unsigned_to_nat(1u);
v___x_288_ = lean_unsigned_to_nat(0u);
v_a_289_ = lean_array_uget_borrowed(v_as_273_, v_i_275_);
v___x_316_ = l_Lean_Syntax_getArg(v_a_289_, v___x_288_);
v___x_317_ = l_Lean_Syntax_isNone(v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = l_Lean_Syntax_getArg(v___x_316_, v___x_288_);
lean_dec(v___x_316_);
v___x_319_ = l_Lean_Syntax_getId(v___x_318_);
lean_dec(v___x_318_);
v___y_300_ = v___x_319_;
goto v___jp_299_;
}
else
{
lean_object* v___x_320_; 
lean_dec(v___x_316_);
v___x_320_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
v___y_300_ = v___x_320_;
goto v___jp_299_;
}
v___jp_290_:
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = l_Lean_Syntax_getArg(v_a_289_, v___x_287_);
v___x_294_ = l_Lean_Syntax_isNone(v___x_293_);
lean_dec(v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_295_, 0, v___y_291_);
lean_ctor_set(v___x_295_, 1, v_str_292_);
v___x_296_ = lean_array_push(v_b_276_, v___x_295_);
v_a_281_ = v___x_296_;
goto v___jp_280_;
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_297_, 0, v___y_291_);
lean_ctor_set(v___x_297_, 1, v_str_292_);
v___x_298_ = lean_array_push(v_b_276_, v___x_297_);
v_a_281_ = v___x_298_;
goto v___jp_280_;
}
}
v___jp_299_:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_301_ = lean_unsigned_to_nat(2u);
v___x_302_ = l_Lean_Syntax_getArg(v_a_289_, v___x_301_);
v___x_303_ = l_Lean_Syntax_isStrLit_x3f(v___x_302_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1);
lean_inc_ref(v___y_277_);
v___x_305_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v___x_302_, v___x_304_, v___y_277_, v___y_278_);
lean_dec(v___x_302_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_a_306_);
lean_dec_ref(v___x_305_);
v___y_291_ = v___y_300_;
v_str_292_ = v_a_306_;
goto v___jp_290_;
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
lean_dec(v___y_300_);
lean_dec_ref(v___y_277_);
lean_dec_ref(v_b_276_);
v_a_307_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_305_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_305_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
else
{
lean_object* v_val_315_; 
lean_dec(v___x_302_);
v_val_315_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_val_315_);
lean_dec_ref(v___x_303_);
v___y_291_ = v___y_300_;
v_str_292_ = v_val_315_;
goto v___jp_290_;
}
}
}
v___jp_280_:
{
size_t v___x_282_; size_t v___x_283_; 
v___x_282_ = ((size_t)1ULL);
v___x_283_ = lean_usize_add(v_i_275_, v___x_282_);
v_i_275_ = v___x_283_;
v_b_276_ = v_a_281_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___boxed(lean_object* v_as_321_, lean_object* v_sz_322_, lean_object* v_i_323_, lean_object* v_b_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
size_t v_sz_boxed_328_; size_t v_i_boxed_329_; lean_object* v_res_330_; 
v_sz_boxed_328_ = lean_unbox_usize(v_sz_322_);
lean_dec(v_sz_322_);
v_i_boxed_329_ = lean_unbox_usize(v_i_323_);
lean_dec(v_i_323_);
v_res_330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(v_as_321_, v_sz_boxed_328_, v_i_boxed_329_, v_b_324_, v___y_325_, v___y_326_);
lean_dec(v___y_326_);
lean_dec_ref(v_as_321_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(lean_object* v_stx_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v_entriesStx_344_; lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_342_ = lean_unsigned_to_nat(1u);
v___x_343_ = l_Lean_Syntax_getArg(v_stx_338_, v___x_342_);
v_entriesStx_344_ = l_Lean_Syntax_getArgs(v___x_343_);
lean_dec(v___x_343_);
v___x_345_ = lean_array_get_size(v_entriesStx_344_);
v___x_346_ = lean_unsigned_to_nat(0u);
v___x_347_ = lean_nat_dec_eq(v___x_345_, v___x_346_);
if (v___x_347_ == 0)
{
lean_object* v_entries_348_; size_t v_sz_349_; size_t v___x_350_; lean_object* v___x_351_; 
v_entries_348_ = ((lean_object*)(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__0));
v_sz_349_ = lean_array_size(v_entriesStx_344_);
v___x_350_ = ((size_t)0ULL);
v___x_351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(v_entriesStx_344_, v_sz_349_, v___x_350_, v_entries_348_, v_a_339_, v_a_340_);
lean_dec_ref(v_entriesStx_344_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_360_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_360_ == 0)
{
v___x_354_ = v___x_351_;
v_isShared_355_ = v_isSharedCheck_360_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_360_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v___x_358_; 
v___x_356_ = lean_array_to_list(v_a_352_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_356_);
v___x_358_ = v___x_354_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_356_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
v_a_361_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_351_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_351_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
else
{
lean_object* v___x_369_; lean_object* v___x_370_; 
lean_dec_ref(v_entriesStx_344_);
lean_dec_ref(v_a_339_);
v___x_369_ = ((lean_object*)(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2));
v___x_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___boxed(lean_object* v_stx_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(v_stx_371_, v_a_372_, v_a_373_);
lean_dec(v_a_373_);
lean_dec(v_stx_371_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(lean_object* v_00_u03b1_376_, lean_object* v_ref_377_, lean_object* v_msg_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v_ref_377_, v_msg_378_, v___y_379_, v___y_380_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___boxed(lean_object* v_00_u03b1_383_, lean_object* v_ref_384_, lean_object* v_msg_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(v_00_u03b1_383_, v_ref_384_, v_msg_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec(v_ref_384_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0(lean_object* v_00_u03b1_390_, lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_391_, v___y_392_, v___y_393_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___boxed(lean_object* v_00_u03b1_396_, lean_object* v_msg_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0(v_00_u03b1_396_, v_msg_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_addExtern___boxed(lean_object* v_declName_407_, lean_object* v_externAttrData_408_, lean_object* v_a_00___x40___internal___hyg_409_, lean_object* v_a_00___x40___internal___hyg_410_, lean_object* v_a_00___x40___internal___hyg_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = lean_add_extern(v_declName_407_, v_externAttrData_408_, v_a_00___x40___internal___hyg_409_, v_a_00___x40___internal___hyg_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_(lean_object* v_x_413_, lean_object* v_stx_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(v_stx_414_, v___y_415_, v___y_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2____boxed(lean_object* v_x_419_, lean_object* v_stx_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_(v_x_419_, v_stx_420_, v___y_421_, v___y_422_);
lean_dec(v___y_422_);
lean_dec(v_stx_420_);
lean_dec(v_x_419_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_(lean_object* v_declName_425_, lean_object* v_externAttrData_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___x_430_; lean_object* v_env_431_; uint8_t v___y_433_; uint8_t v___x_450_; 
v___x_430_ = lean_st_ref_get(v___y_428_);
v_env_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc_ref(v_env_431_);
lean_dec(v___x_430_);
lean_inc(v_declName_425_);
lean_inc_ref(v_env_431_);
v___x_450_ = l_Lean_Environment_isProjectionFn(v_env_431_, v_declName_425_);
if (v___x_450_ == 0)
{
uint8_t v___x_451_; 
lean_inc(v_declName_425_);
lean_inc_ref(v_env_431_);
v___x_451_ = l_Lean_Environment_isConstructor(v_env_431_, v_declName_425_);
v___y_433_ = v___x_451_;
goto v___jp_432_;
}
else
{
v___y_433_ = v___x_450_;
goto v___jp_432_;
}
v___jp_432_:
{
if (v___y_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec_ref(v_env_431_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v_externAttrData_426_);
lean_dec(v_declName_425_);
v___x_434_ = lean_box(0);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
else
{
uint8_t v___x_436_; lean_object* v___x_437_; 
v___x_436_ = 0;
lean_inc(v_declName_425_);
v___x_437_ = l_Lean_Environment_find_x3f(v_env_431_, v_declName_425_, v___x_436_);
if (lean_obj_tag(v___x_437_) == 1)
{
lean_object* v_val_438_; 
v_val_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_val_438_);
lean_dec_ref(v___x_437_);
if (lean_obj_tag(v_val_438_) == 2)
{
lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_446_; 
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v_externAttrData_426_);
lean_dec(v_declName_425_);
v_isSharedCheck_446_ = !lean_is_exclusive(v_val_438_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; 
v_unused_447_ = lean_ctor_get(v_val_438_, 0);
lean_dec(v_unused_447_);
v___x_440_ = v_val_438_;
v_isShared_441_ = v_isSharedCheck_446_;
goto v_resetjp_439_;
}
else
{
lean_dec(v_val_438_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_446_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_442_ = lean_box(0);
if (v_isShared_441_ == 0)
{
lean_ctor_set_tag(v___x_440_, 0);
lean_ctor_set(v___x_440_, 0, v___x_442_);
v___x_444_ = v___x_440_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
else
{
lean_object* v___x_448_; 
lean_dec(v_val_438_);
v___x_448_ = lean_add_extern(v_declName_425_, v_externAttrData_426_, v___y_427_, v___y_428_);
return v___x_448_;
}
}
else
{
lean_object* v___x_449_; 
lean_dec(v___x_437_);
v___x_449_ = lean_add_extern(v_declName_425_, v_externAttrData_426_, v___y_427_, v___y_428_);
return v___x_449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2____boxed(lean_object* v_declName_452_, lean_object* v_externAttrData_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_(v_declName_452_, v_externAttrData_453_, v___y_454_, v___y_455_);
return v_res_457_;
}
}
LEAN_EXPORT uint8_t l_Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_(uint8_t v___x_458_, lean_object* v_env_459_, lean_object* v_n_460_, lean_object* v_x_461_){
_start:
{
uint8_t v___x_462_; 
v___x_462_ = l_Lean_Environment_contains(v_env_459_, v_n_460_, v___x_458_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2____boxed(lean_object* v___x_463_, lean_object* v_env_464_, lean_object* v_n_465_, lean_object* v_x_466_){
_start:
{
uint8_t v___x_820__boxed_467_; uint8_t v_res_468_; lean_object* v_r_469_; 
v___x_820__boxed_467_ = lean_unbox(v___x_463_);
v_res_468_ = l_Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_(v___x_820__boxed_467_, v_env_464_, v_n_465_, v_x_466_);
lean_dec(v_x_466_);
v_r_469_ = lean_box(v_res_468_);
return v_r_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = ((lean_object*)(l_Lean_initFn___closed__10_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_));
v___x_497_ = l_Lean_registerParametricAttribute___redArg(v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2____boxed(lean_object* v_a_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_initFn_00___x40_Lean_Compiler_ExternAttr_4197872175____hygCtx___hyg_2_();
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternAttrData_x3f(lean_object* v_env_500_, lean_object* v_n_501_){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_502_ = lean_box(0);
v___x_503_ = l_Lean_externAttr;
v___x_504_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_502_, v___x_503_, v_env_500_, v_n_501_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(lean_object* v_x_505_, lean_object* v_x_506_, lean_object* v_x_507_, lean_object* v_x_508_){
_start:
{
lean_object* v_zero_509_; uint8_t v_isZero_510_; 
v_zero_509_ = lean_unsigned_to_nat(0u);
v_isZero_510_ = lean_nat_dec_eq(v_x_505_, v_zero_509_);
if (v_isZero_510_ == 1)
{
lean_object* v___x_511_; 
lean_dec(v_x_505_);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v_x_507_);
lean_ctor_set(v___x_511_, 1, v_x_508_);
return v___x_511_;
}
else
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = lean_string_utf8_byte_size(v_x_506_);
v___x_513_ = lean_nat_dec_eq(v_x_507_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v_one_514_; lean_object* v_n_515_; uint32_t v_c_516_; uint8_t v___y_518_; uint32_t v___x_528_; uint8_t v___x_529_; 
v_one_514_ = lean_unsigned_to_nat(1u);
v_n_515_ = lean_nat_sub(v_x_505_, v_one_514_);
lean_dec(v_x_505_);
v_c_516_ = lean_string_utf8_get_fast(v_x_506_, v_x_507_);
v___x_528_ = 48;
v___x_529_ = lean_uint32_dec_le(v___x_528_, v_c_516_);
if (v___x_529_ == 0)
{
v___y_518_ = v___x_529_;
goto v___jp_517_;
}
else
{
uint32_t v___x_530_; uint8_t v___x_531_; 
v___x_530_ = 57;
v___x_531_ = lean_uint32_dec_le(v_c_516_, v___x_530_);
v___y_518_ = v___x_531_;
goto v___jp_517_;
}
v___jp_517_:
{
if (v___y_518_ == 0)
{
lean_object* v___x_519_; 
lean_dec(v_n_515_);
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v_x_507_);
lean_ctor_set(v___x_519_, 1, v_x_508_);
return v___x_519_;
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_520_ = lean_string_utf8_next_fast(v_x_506_, v_x_507_);
lean_dec(v_x_507_);
v___x_521_ = lean_unsigned_to_nat(10u);
v___x_522_ = lean_nat_mul(v_x_508_, v___x_521_);
lean_dec(v_x_508_);
v___x_523_ = lean_uint32_to_nat(v_c_516_);
v___x_524_ = lean_unsigned_to_nat(48u);
v___x_525_ = lean_nat_sub(v___x_523_, v___x_524_);
lean_dec(v___x_523_);
v___x_526_ = lean_nat_add(v___x_522_, v___x_525_);
lean_dec(v___x_525_);
lean_dec(v___x_522_);
v_x_505_ = v_n_515_;
v_x_507_ = v___x_520_;
v_x_508_ = v___x_526_;
goto _start;
}
}
}
else
{
lean_object* v___x_532_; 
lean_dec(v_x_505_);
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v_x_507_);
lean_ctor_set(v___x_532_, 1, v_x_508_);
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum___boxed(lean_object* v_x_533_, lean_object* v_x_534_, lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(v_x_533_, v_x_534_, v_x_535_, v_x_536_);
lean_dec_ref(v_x_534_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux(lean_object* v_args_539_, lean_object* v_x_540_, lean_object* v_x_541_, lean_object* v_x_542_, lean_object* v_x_543_){
_start:
{
lean_object* v_zero_544_; uint8_t v_isZero_545_; 
v_zero_544_ = lean_unsigned_to_nat(0u);
v_isZero_545_ = lean_nat_dec_eq(v_x_540_, v_zero_544_);
if (v_isZero_545_ == 1)
{
lean_dec(v_x_542_);
lean_dec_ref(v_x_541_);
lean_dec(v_x_540_);
return v_x_543_;
}
else
{
lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_546_ = lean_string_utf8_byte_size(v_x_541_);
v___x_547_ = lean_nat_dec_eq(v_x_542_, v___x_546_);
if (v___x_547_ == 0)
{
lean_object* v_one_548_; lean_object* v_n_549_; uint32_t v_c_550_; uint32_t v___x_555_; uint8_t v___x_556_; 
v_one_548_ = lean_unsigned_to_nat(1u);
v_n_549_ = lean_nat_sub(v_x_540_, v_one_548_);
lean_dec(v_x_540_);
v_c_550_ = lean_string_utf8_get_fast(v_x_541_, v_x_542_);
v___x_555_ = 35;
v___x_556_ = lean_uint32_dec_eq(v_c_550_, v___x_555_);
if (v___x_556_ == 0)
{
goto v___jp_551_;
}
else
{
if (v___x_547_ == 0)
{
lean_object* v_it_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v_fst_560_; lean_object* v_snd_561_; lean_object* v_j_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_it_557_ = lean_string_utf8_next_fast(v_x_541_, v_x_542_);
lean_dec(v_x_542_);
lean_inc_ref(v_x_541_);
v___x_558_ = l_String_Pos_remainingBytes(v_x_541_, v_it_557_);
v___x_559_ = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(v___x_558_, v_x_541_, v_it_557_, v_zero_544_);
v_fst_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_fst_560_);
v_snd_561_ = lean_ctor_get(v___x_559_, 1);
lean_inc(v_snd_561_);
lean_dec_ref(v___x_559_);
v_j_562_ = lean_nat_sub(v_snd_561_, v_one_548_);
lean_dec(v_snd_561_);
v___x_563_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_564_ = l_List_getD___redArg(v_args_539_, v_j_562_, v___x_563_);
v___x_565_ = lean_string_append(v_x_543_, v___x_564_);
lean_dec(v___x_564_);
v_x_540_ = v_n_549_;
v_x_542_ = v_fst_560_;
v_x_543_ = v___x_565_;
goto _start;
}
else
{
goto v___jp_551_;
}
}
v___jp_551_:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_string_utf8_next_fast(v_x_541_, v_x_542_);
lean_dec(v_x_542_);
v___x_553_ = lean_string_push(v_x_543_, v_c_550_);
v_x_540_ = v_n_549_;
v_x_542_ = v___x_552_;
v_x_543_ = v___x_553_;
goto _start;
}
}
else
{
lean_dec(v_x_542_);
lean_dec_ref(v_x_541_);
lean_dec(v_x_540_);
return v_x_543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux___boxed(lean_object* v_args_567_, lean_object* v_x_568_, lean_object* v_x_569_, lean_object* v_x_570_, lean_object* v_x_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_expandExternPatternAux(v_args_567_, v_x_568_, v_x_569_, v_x_570_, v_x_571_);
lean_dec(v_args_567_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPattern(lean_object* v_pattern_573_, lean_object* v_args_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_575_ = lean_string_length(v_pattern_573_);
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_578_ = l_Lean_expandExternPatternAux(v_args_574_, v___x_575_, v_pattern_573_, v___x_576_, v___x_577_);
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
LEAN_EXPORT uint8_t l_Lean_getExternEntryForAux___lam__0(lean_object* v_backend_610_, lean_object* v_e_611_){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_612_ = l_Lean_ExternEntry_backend(v_e_611_);
v___x_613_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
v___x_614_ = lean_name_eq(v___x_612_, v___x_613_);
if (v___x_614_ == 0)
{
uint8_t v___x_615_; 
v___x_615_ = lean_name_eq(v___x_612_, v_backend_610_);
lean_dec(v___x_612_);
return v___x_615_;
}
else
{
lean_dec(v___x_612_);
return v___x_614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux___lam__0___boxed(lean_object* v_backend_616_, lean_object* v_e_617_){
_start:
{
uint8_t v_res_618_; lean_object* v_r_619_; 
v_res_618_ = l_Lean_getExternEntryForAux___lam__0(v_backend_616_, v_e_617_);
lean_dec(v_e_617_);
lean_dec(v_backend_616_);
v_r_619_ = lean_box(v_res_618_);
return v_r_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux(lean_object* v_backend_620_, lean_object* v_entries_621_){
_start:
{
lean_object* v___f_622_; lean_object* v___x_623_; 
v___f_622_ = lean_alloc_closure((void*)(l_Lean_getExternEntryForAux___lam__0___boxed), 2, 1);
lean_closure_set(v___f_622_, 0, v_backend_620_);
v___x_623_ = l_List_find_x3f___redArg(v___f_622_, v_entries_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor(lean_object* v_d_624_, lean_object* v_backend_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_getExternEntryForAux(v_backend_625_, v_d_624_);
return v___x_626_;
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
lean_dec_ref(v___x_629_);
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
lean_dec_ref(v___x_638_);
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
lean_dec_ref(v_val_639_);
v_str_644_ = lean_ctor_get(v_backend_641_, 1);
lean_inc_ref(v_str_644_);
lean_dec_ref(v_backend_641_);
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
lean_dec_ref(v_backend_641_);
lean_dec_ref(v_val_639_);
v___x_648_ = 0;
return v___x_648_;
}
}
else
{
uint8_t v___x_649_; 
lean_dec(v_backend_641_);
lean_dec_ref(v_val_639_);
v___x_649_ = 0;
return v___x_649_;
}
}
else
{
uint8_t v___x_650_; 
lean_dec_ref(v_val_639_);
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
lean_dec(v_backend_658_);
v___x_661_ = lean_box(0);
return v___x_661_;
}
else
{
lean_object* v_val_662_; lean_object* v___x_663_; 
v_val_662_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_val_662_);
lean_dec_ref(v___x_660_);
v___x_663_ = l_Lean_getExternEntryForAux(v_backend_658_, v_val_662_);
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
lean_dec_ref(v_val_665_);
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
