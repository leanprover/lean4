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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_intersperseTR___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
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
LEAN_EXPORT uint8_t l_Lean_instBEqExternEntry_beq(lean_object* v_x_56_, lean_object* v_x_57_){
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
LEAN_EXPORT lean_object* l_Lean_instBEqExternEntry_beq___boxed(lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
uint8_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = l_Lean_instBEqExternEntry_beq(v_x_81_, v_x_82_);
lean_dec(v_x_82_);
lean_dec(v_x_81_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableExternEntry_hash(lean_object* v_x_87_){
_start:
{
switch(lean_obj_tag(v_x_87_))
{
case 0:
{
lean_object* v_backend_88_; uint64_t v___x_89_; 
v_backend_88_ = lean_ctor_get(v_x_87_, 0);
v___x_89_ = 0ULL;
if (lean_obj_tag(v_backend_88_) == 0)
{
uint64_t v___x_90_; 
v___x_90_ = 8934034000889494153ULL;
return v___x_90_;
}
else
{
uint64_t v_hash_91_; uint64_t v___x_92_; 
v_hash_91_ = lean_ctor_get_uint64(v_backend_88_, sizeof(void*)*2);
v___x_92_ = lean_uint64_mix_hash(v___x_89_, v_hash_91_);
return v___x_92_;
}
}
case 1:
{
lean_object* v_backend_93_; lean_object* v_pattern_94_; uint64_t v___x_95_; uint64_t v___y_97_; 
v_backend_93_ = lean_ctor_get(v_x_87_, 0);
v_pattern_94_ = lean_ctor_get(v_x_87_, 1);
v___x_95_ = 1ULL;
if (lean_obj_tag(v_backend_93_) == 0)
{
uint64_t v___x_101_; 
v___x_101_ = 1723ULL;
v___y_97_ = v___x_101_;
goto v___jp_96_;
}
else
{
uint64_t v_hash_102_; 
v_hash_102_ = lean_ctor_get_uint64(v_backend_93_, sizeof(void*)*2);
v___y_97_ = v_hash_102_;
goto v___jp_96_;
}
v___jp_96_:
{
uint64_t v___x_98_; uint64_t v___x_99_; uint64_t v___x_100_; 
v___x_98_ = lean_uint64_mix_hash(v___x_95_, v___y_97_);
v___x_99_ = lean_string_hash(v_pattern_94_);
v___x_100_ = lean_uint64_mix_hash(v___x_98_, v___x_99_);
return v___x_100_;
}
}
case 2:
{
lean_object* v_backend_103_; lean_object* v_fn_104_; uint64_t v___x_105_; uint64_t v___y_107_; 
v_backend_103_ = lean_ctor_get(v_x_87_, 0);
v_fn_104_ = lean_ctor_get(v_x_87_, 1);
v___x_105_ = 2ULL;
if (lean_obj_tag(v_backend_103_) == 0)
{
uint64_t v___x_111_; 
v___x_111_ = 1723ULL;
v___y_107_ = v___x_111_;
goto v___jp_106_;
}
else
{
uint64_t v_hash_112_; 
v_hash_112_ = lean_ctor_get_uint64(v_backend_103_, sizeof(void*)*2);
v___y_107_ = v_hash_112_;
goto v___jp_106_;
}
v___jp_106_:
{
uint64_t v___x_108_; uint64_t v___x_109_; uint64_t v___x_110_; 
v___x_108_ = lean_uint64_mix_hash(v___x_105_, v___y_107_);
v___x_109_ = lean_string_hash(v_fn_104_);
v___x_110_ = lean_uint64_mix_hash(v___x_108_, v___x_109_);
return v___x_110_;
}
}
default: 
{
uint64_t v___x_113_; 
v___x_113_ = 3ULL;
return v___x_113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableExternEntry_hash___boxed(lean_object* v_x_114_){
_start:
{
uint64_t v_res_115_; lean_object* v_r_116_; 
v_res_115_ = l_Lean_instHashableExternEntry_hash(v_x_114_);
lean_dec(v_x_114_);
v_r_116_ = lean_box_uint64(v_res_115_);
return v_r_116_;
}
}
static lean_object* _init_l_Lean_instInhabitedExternAttrData_default(void){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_box(0);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_instInhabitedExternAttrData(void){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_box(0);
return v___x_120_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0(lean_object* v_x_121_, lean_object* v_x_122_){
_start:
{
if (lean_obj_tag(v_x_121_) == 0)
{
if (lean_obj_tag(v_x_122_) == 0)
{
uint8_t v___x_123_; 
v___x_123_ = 1;
return v___x_123_;
}
else
{
uint8_t v___x_124_; 
v___x_124_ = 0;
return v___x_124_;
}
}
else
{
if (lean_obj_tag(v_x_122_) == 0)
{
uint8_t v___x_125_; 
v___x_125_ = 0;
return v___x_125_;
}
else
{
lean_object* v_head_126_; lean_object* v_tail_127_; lean_object* v_head_128_; lean_object* v_tail_129_; uint8_t v___x_130_; 
v_head_126_ = lean_ctor_get(v_x_121_, 0);
v_tail_127_ = lean_ctor_get(v_x_121_, 1);
v_head_128_ = lean_ctor_get(v_x_122_, 0);
v_tail_129_ = lean_ctor_get(v_x_122_, 1);
v___x_130_ = l_Lean_instBEqExternEntry_beq(v_head_126_, v_head_128_);
if (v___x_130_ == 0)
{
return v___x_130_;
}
else
{
v_x_121_ = v_tail_127_;
v_x_122_ = v_tail_129_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0___boxed(lean_object* v_x_132_, lean_object* v_x_133_){
_start:
{
uint8_t v_res_134_; lean_object* v_r_135_; 
v_res_134_ = l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0(v_x_132_, v_x_133_);
lean_dec(v_x_133_);
lean_dec(v_x_132_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqExternAttrData_beq(lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
uint8_t v___x_138_; 
v___x_138_ = l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0(v_x_136_, v_x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqExternAttrData_beq___boxed(lean_object* v_x_139_, lean_object* v_x_140_){
_start:
{
uint8_t v_res_141_; lean_object* v_r_142_; 
v_res_141_ = l_Lean_instBEqExternAttrData_beq(v_x_139_, v_x_140_);
lean_dec(v_x_140_);
lean_dec(v_x_139_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0(uint64_t v_x_145_, lean_object* v_x_146_){
_start:
{
if (lean_obj_tag(v_x_146_) == 0)
{
return v_x_145_;
}
else
{
lean_object* v_head_147_; lean_object* v_tail_148_; uint64_t v___x_149_; uint64_t v___x_150_; 
v_head_147_ = lean_ctor_get(v_x_146_, 0);
v_tail_148_ = lean_ctor_get(v_x_146_, 1);
v___x_149_ = l_Lean_instHashableExternEntry_hash(v_head_147_);
v___x_150_ = lean_uint64_mix_hash(v_x_145_, v___x_149_);
v_x_145_ = v___x_150_;
v_x_146_ = v_tail_148_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0___boxed(lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
uint64_t v_x_57__boxed_154_; uint64_t v_res_155_; lean_object* v_r_156_; 
v_x_57__boxed_154_ = lean_unbox_uint64(v_x_152_);
lean_dec_ref(v_x_152_);
v_res_155_ = l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0(v_x_57__boxed_154_, v_x_153_);
lean_dec(v_x_153_);
v_r_156_ = lean_box_uint64(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableExternAttrData_hash(lean_object* v_x_157_){
_start:
{
uint64_t v___x_158_; uint64_t v___x_159_; uint64_t v___x_160_; uint64_t v___x_161_; 
v___x_158_ = 0ULL;
v___x_159_ = 7ULL;
v___x_160_ = l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0(v___x_159_, v_x_157_);
v___x_161_ = lean_uint64_mix_hash(v___x_158_, v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableExternAttrData_hash___boxed(lean_object* v_x_162_){
_start:
{
uint64_t v_res_163_; lean_object* v_r_164_; 
v_res_163_ = l_Lean_instHashableExternAttrData_hash(v_x_162_);
lean_dec(v_x_162_);
v_r_164_ = lean_box_uint64(v_res_163_);
return v_r_164_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_167_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__0);
v___x_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
return v___x_169_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1);
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
lean_ctor_set(v___x_172_, 2, v___x_171_);
lean_ctor_set(v___x_172_, 3, v___x_171_);
lean_ctor_set(v___x_172_, 4, v___x_170_);
lean_ctor_set(v___x_172_, 5, v___x_170_);
lean_ctor_set(v___x_172_, 6, v___x_170_);
lean_ctor_set(v___x_172_, 7, v___x_170_);
lean_ctor_set(v___x_172_, 8, v___x_170_);
lean_ctor_set(v___x_172_, 9, v___x_170_);
lean_ctor_set(v___x_172_, 10, v___x_170_);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = lean_unsigned_to_nat(32u);
v___x_174_ = lean_mk_empty_array_with_capacity(v___x_173_);
v___x_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
return v___x_175_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_176_ = ((size_t)5ULL);
v___x_177_ = lean_unsigned_to_nat(0u);
v___x_178_ = lean_unsigned_to_nat(32u);
v___x_179_ = lean_mk_empty_array_with_capacity(v___x_178_);
v___x_180_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3);
v___x_181_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___x_179_);
lean_ctor_set(v___x_181_, 2, v___x_177_);
lean_ctor_set(v___x_181_, 3, v___x_177_);
lean_ctor_set_usize(v___x_181_, 4, v___x_176_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_182_ = lean_box(1);
v___x_183_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4);
v___x_184_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1);
v___x_185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___x_183_);
lean_ctor_set(v___x_185_, 2, v___x_182_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1(lean_object* v_msgData_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___x_190_; lean_object* v_toCold_191_; lean_object* v_env_192_; lean_object* v_options_193_; uint8_t v___x_194_; lean_object* v_env_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_190_ = lean_st_ref_get(v___y_188_);
v_toCold_191_ = lean_ctor_get(v___y_187_, 0);
v_env_192_ = lean_ctor_get(v___x_190_, 0);
lean_inc_ref(v_env_192_);
lean_dec(v___x_190_);
v_options_193_ = lean_ctor_get(v_toCold_191_, 2);
v___x_194_ = 0;
v_env_195_ = l_Lean_Environment_setRecordingDeps(v_env_192_, v___x_194_);
v___x_196_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2);
v___x_197_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_193_);
v___x_198_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_198_, 0, v_env_195_);
lean_ctor_set(v___x_198_, 1, v___x_196_);
lean_ctor_set(v___x_198_, 2, v___x_197_);
lean_ctor_set(v___x_198_, 3, v_options_193_);
v___x_199_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v_msgData_186_);
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1(v_msgData_201_, v___y_202_, v___y_203_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(lean_object* v_msg_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_ref_210_; lean_object* v___x_211_; lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_220_; 
v_ref_210_ = lean_ctor_get(v___y_207_, 2);
v___x_211_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1(v_msg_206_, v___y_207_, v___y_208_);
v_a_212_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_220_ == 0)
{
v___x_214_ = v___x_211_;
v_isShared_215_ = v_isSharedCheck_220_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_211_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_220_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v___x_218_; 
lean_inc(v_ref_210_);
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v_ref_210_);
lean_ctor_set(v___x_216_, 1, v_a_212_);
if (v_isShared_215_ == 0)
{
lean_ctor_set_tag(v___x_214_, 1);
lean_ctor_set(v___x_214_, 0, v___x_216_);
v___x_218_ = v___x_214_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg___boxed(lean_object* v_msg_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_221_, v___y_222_, v___y_223_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(lean_object* v_ref_226_, lean_object* v_msg_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_toCold_231_; lean_object* v_currRecDepth_232_; lean_object* v_ref_233_; uint16_t v_optionFlags_234_; uint8_t v_suppressElabErrors_235_; uint8_t v_checkDeprecated_236_; uint8_t v_isRecordingDeps_237_; lean_object* v_ref_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_toCold_231_ = lean_ctor_get(v___y_228_, 0);
v_currRecDepth_232_ = lean_ctor_get(v___y_228_, 1);
v_ref_233_ = lean_ctor_get(v___y_228_, 2);
v_optionFlags_234_ = lean_ctor_get_uint16(v___y_228_, sizeof(void*)*3);
v_suppressElabErrors_235_ = lean_ctor_get_uint8(v___y_228_, sizeof(void*)*3 + 2);
v_checkDeprecated_236_ = lean_ctor_get_uint8(v___y_228_, sizeof(void*)*3 + 3);
v_isRecordingDeps_237_ = lean_ctor_get_uint8(v___y_228_, sizeof(void*)*3 + 4);
v_ref_238_ = l_Lean_replaceRef(v_ref_226_, v_ref_233_);
lean_inc(v_currRecDepth_232_);
lean_inc_ref(v_toCold_231_);
v___x_239_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_239_, 0, v_toCold_231_);
lean_ctor_set(v___x_239_, 1, v_currRecDepth_232_);
lean_ctor_set(v___x_239_, 2, v_ref_238_);
lean_ctor_set_uint16(v___x_239_, sizeof(void*)*3, v_optionFlags_234_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*3 + 2, v_suppressElabErrors_235_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*3 + 3, v_checkDeprecated_236_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*3 + 4, v_isRecordingDeps_237_);
v___x_240_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_227_, v___x_239_, v___y_229_);
lean_dec_ref_known(v___x_239_, 3);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg___boxed(lean_object* v_ref_241_, lean_object* v_msg_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v_ref_241_, v_msg_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v_ref_241_);
return v_res_246_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__0));
v___x_249_ = l_Lean_stringToMessageData(v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(lean_object* v_as_253_, size_t v_sz_254_, size_t v_i_255_, lean_object* v_b_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_a_261_; uint8_t v___x_265_; 
v___x_265_ = lean_usize_dec_lt(v_i_255_, v_sz_254_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; 
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v_b_256_);
return v___x_266_;
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v_a_269_; lean_object* v___y_271_; lean_object* v_str_272_; lean_object* v___y_280_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_267_ = lean_unsigned_to_nat(1u);
v___x_268_ = lean_unsigned_to_nat(0u);
v_a_269_ = lean_array_uget_borrowed(v_as_253_, v_i_255_);
v___x_296_ = l_Lean_Syntax_getArg(v_a_269_, v___x_268_);
v___x_297_ = l_Lean_Syntax_isNone(v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = l_Lean_Syntax_getArg(v___x_296_, v___x_268_);
lean_dec(v___x_296_);
v___x_299_ = l_Lean_Syntax_getId(v___x_298_);
lean_dec(v___x_298_);
v___y_280_ = v___x_299_;
goto v___jp_279_;
}
else
{
lean_object* v___x_300_; 
lean_dec(v___x_296_);
v___x_300_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
v___y_280_ = v___x_300_;
goto v___jp_279_;
}
v___jp_270_:
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = l_Lean_Syntax_getArg(v_a_269_, v___x_267_);
v___x_274_ = l_Lean_Syntax_isNone(v___x_273_);
lean_dec(v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_275_, 0, v___y_271_);
lean_ctor_set(v___x_275_, 1, v_str_272_);
v___x_276_ = lean_array_push(v_b_256_, v___x_275_);
v_a_261_ = v___x_276_;
goto v___jp_260_;
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_277_, 0, v___y_271_);
lean_ctor_set(v___x_277_, 1, v_str_272_);
v___x_278_ = lean_array_push(v_b_256_, v___x_277_);
v_a_261_ = v___x_278_;
goto v___jp_260_;
}
}
v___jp_279_:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = lean_unsigned_to_nat(2u);
v___x_282_ = l_Lean_Syntax_getArg(v_a_269_, v___x_281_);
v___x_283_ = l_Lean_Syntax_isStrLit_x3f(v___x_282_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1);
v___x_285_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v___x_282_, v___x_284_, v___y_257_, v___y_258_);
lean_dec(v___x_282_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_a_286_);
lean_dec_ref_known(v___x_285_, 1);
v___y_271_ = v___y_280_;
v_str_272_ = v_a_286_;
goto v___jp_270_;
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
lean_dec(v___y_280_);
lean_dec_ref(v_b_256_);
v_a_287_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_285_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_285_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
else
{
lean_object* v_val_295_; 
lean_dec(v___x_282_);
v_val_295_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_val_295_);
lean_dec_ref_known(v___x_283_, 1);
v___y_271_ = v___y_280_;
v_str_272_ = v_val_295_;
goto v___jp_270_;
}
}
}
v___jp_260_:
{
size_t v___x_262_; size_t v___x_263_; 
v___x_262_ = ((size_t)1ULL);
v___x_263_ = lean_usize_add(v_i_255_, v___x_262_);
v_i_255_ = v___x_263_;
v_b_256_ = v_a_261_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___boxed(lean_object* v_as_301_, lean_object* v_sz_302_, lean_object* v_i_303_, lean_object* v_b_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
size_t v_sz_boxed_308_; size_t v_i_boxed_309_; lean_object* v_res_310_; 
v_sz_boxed_308_ = lean_unbox_usize(v_sz_302_);
lean_dec(v_sz_302_);
v_i_boxed_309_ = lean_unbox_usize(v_i_303_);
lean_dec(v_i_303_);
v_res_310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(v_as_301_, v_sz_boxed_308_, v_i_boxed_309_, v_b_304_, v___y_305_, v___y_306_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec_ref(v_as_301_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(lean_object* v_stx_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v_entriesStx_324_; lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = l_Lean_Syntax_getArg(v_stx_318_, v___x_322_);
v_entriesStx_324_ = l_Lean_Syntax_getArgs(v___x_323_);
lean_dec(v___x_323_);
v___x_325_ = lean_array_get_size(v_entriesStx_324_);
v___x_326_ = lean_unsigned_to_nat(0u);
v___x_327_ = lean_nat_dec_eq(v___x_325_, v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v_entries_328_; size_t v_sz_329_; size_t v___x_330_; lean_object* v___x_331_; 
v_entries_328_ = ((lean_object*)(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__0));
v_sz_329_ = lean_array_size(v_entriesStx_324_);
v___x_330_ = ((size_t)0ULL);
v___x_331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(v_entriesStx_324_, v_sz_329_, v___x_330_, v_entries_328_, v_a_319_, v_a_320_);
lean_dec_ref(v_entriesStx_324_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_340_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_340_ == 0)
{
v___x_334_ = v___x_331_;
v_isShared_335_ = v_isSharedCheck_340_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_331_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_340_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_336_ = lean_array_to_list(v_a_332_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_336_);
v___x_338_ = v___x_334_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
v_a_341_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_331_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_331_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec_ref(v_entriesStx_324_);
v___x_349_ = ((lean_object*)(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2));
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___boxed(lean_object* v_stx_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(v_stx_351_, v_a_352_, v_a_353_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_stx_351_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(lean_object* v_00_u03b1_356_, lean_object* v_ref_357_, lean_object* v_msg_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v_ref_357_, v_msg_358_, v___y_359_, v___y_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___boxed(lean_object* v_00_u03b1_363_, lean_object* v_ref_364_, lean_object* v_msg_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(v_00_u03b1_363_, v_ref_364_, v_msg_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v_ref_364_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0(lean_object* v_00_u03b1_370_, lean_object* v_msg_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_371_, v___y_372_, v___y_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___boxed(lean_object* v_00_u03b1_376_, lean_object* v_msg_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0(v_00_u03b1_376_, v_msg_377_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(lean_object* v_x_382_, lean_object* v_stx_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(v_stx_383_, v___y_384_, v___y_385_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v_x_388_, lean_object* v_stx_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v_x_388_, v_stx_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v_stx_389_);
lean_dec(v_x_388_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(lean_object* v_declName_394_, lean_object* v_externAttrData_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
uint8_t v___y_400_; lean_object* v___x_405_; lean_object* v_env_406_; uint8_t v___x_421_; 
v___x_405_ = lean_st_ref_get(v___y_397_);
v_env_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc_ref_n(v_env_406_, 2);
lean_dec(v___x_405_);
lean_inc(v_declName_394_);
v___x_421_ = l_Lean_Environment_isProjectionFn(v_env_406_, v_declName_394_);
if (v___x_421_ == 0)
{
uint8_t v___x_422_; 
lean_inc(v_declName_394_);
lean_inc_ref(v_env_406_);
v___x_422_ = l_Lean_Environment_isConstructor(v_env_406_, v_declName_394_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec_ref(v_env_406_);
lean_dec(v_declName_394_);
v___x_423_ = lean_box(0);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
else
{
goto v___jp_407_;
}
}
else
{
goto v___jp_407_;
}
v___jp_399_:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_401_ = lean_unsigned_to_nat(1u);
v___x_402_ = lean_mk_empty_array_with_capacity(v___x_401_);
v___x_403_ = lean_array_push(v___x_402_, v_declName_394_);
v___x_404_ = l_Lean_compileDecls(v___x_403_, v___y_400_, v___y_396_, v___y_397_);
return v___x_404_;
}
v___jp_407_:
{
uint8_t v___x_408_; uint8_t v___x_409_; lean_object* v___x_410_; 
v___x_408_ = 1;
v___x_409_ = 0;
lean_inc(v_declName_394_);
v___x_410_ = l_Lean_Environment_find_x3f(v_env_406_, v_declName_394_, v___x_409_);
if (lean_obj_tag(v___x_410_) == 1)
{
lean_object* v_val_411_; 
v_val_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_val_411_);
lean_dec_ref_known(v___x_410_, 1);
if (lean_obj_tag(v_val_411_) == 2)
{
lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_419_; 
lean_dec(v_declName_394_);
v_isSharedCheck_419_ = !lean_is_exclusive(v_val_411_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; 
v_unused_420_ = lean_ctor_get(v_val_411_, 0);
lean_dec(v_unused_420_);
v___x_413_ = v_val_411_;
v_isShared_414_ = v_isSharedCheck_419_;
goto v_resetjp_412_;
}
else
{
lean_dec(v_val_411_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_419_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_415_ = lean_box(0);
if (v_isShared_414_ == 0)
{
lean_ctor_set_tag(v___x_413_, 0);
lean_ctor_set(v___x_413_, 0, v___x_415_);
v___x_417_ = v___x_413_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
else
{
lean_dec(v_val_411_);
v___y_400_ = v___x_408_;
goto v___jp_399_;
}
}
else
{
lean_dec(v___x_410_);
v___y_400_ = v___x_408_;
goto v___jp_399_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v_declName_425_, lean_object* v_externAttrData_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v_declName_425_, v_externAttrData_426_, v___y_427_, v___y_428_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v_externAttrData_426_);
return v_res_430_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(lean_object* v_env_431_, lean_object* v_n_432_, lean_object* v_x_433_){
_start:
{
uint8_t v___x_434_; uint8_t v___x_435_; 
v___x_434_ = 1;
v___x_435_ = l_Lean_Environment_contains(v_env_431_, v_n_432_, v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v_env_436_, lean_object* v_n_437_, lean_object* v_x_438_){
_start:
{
uint8_t v_res_439_; lean_object* v_r_440_; 
v_res_439_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v_env_436_, v_n_437_, v_x_438_);
lean_dec(v_x_438_);
v_r_440_ = lean_box(v_res_439_);
return v_r_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = ((lean_object*)(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_));
v___x_466_ = l_Lean_registerParametricAttribute___redArg(v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_();
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternAttrData_x3f(lean_object* v_env_469_, lean_object* v_n_470_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = lean_box(0);
v___x_472_ = l_Lean_externAttr;
v___x_473_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_471_, v___x_472_, v_env_469_, v_n_470_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(lean_object* v_pattern_474_, lean_object* v_it_475_, lean_object* v_r_476_){
_start:
{
lean_object* v_str_477_; lean_object* v_startInclusive_478_; lean_object* v_endExclusive_479_; lean_object* v___x_480_; uint8_t v_decide_481_; 
v_str_477_ = lean_ctor_get(v_pattern_474_, 0);
v_startInclusive_478_ = lean_ctor_get(v_pattern_474_, 1);
v_endExclusive_479_ = lean_ctor_get(v_pattern_474_, 2);
v___x_480_ = lean_nat_sub(v_endExclusive_479_, v_startInclusive_478_);
v_decide_481_ = lean_nat_dec_eq(v_it_475_, v___x_480_);
lean_dec(v___x_480_);
if (v_decide_481_ == 0)
{
lean_object* v___x_482_; uint32_t v_c_483_; uint32_t v___x_484_; uint8_t v___x_485_; 
v___x_482_ = lean_nat_add(v_startInclusive_478_, v_it_475_);
v_c_483_ = lean_string_utf8_get_fast(v_str_477_, v___x_482_);
v___x_484_ = 48;
v___x_485_ = lean_uint32_dec_le(v___x_484_, v_c_483_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; 
lean_dec(v___x_482_);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v_it_475_);
lean_ctor_set(v___x_486_, 1, v_r_476_);
return v___x_486_;
}
else
{
uint32_t v___x_487_; uint8_t v___x_488_; 
v___x_487_ = 57;
v___x_488_ = lean_uint32_dec_le(v_c_483_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; 
lean_dec(v___x_482_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v_it_475_);
lean_ctor_set(v___x_489_, 1, v_r_476_);
return v___x_489_;
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec(v_it_475_);
v___x_490_ = lean_string_utf8_next_fast(v_str_477_, v___x_482_);
lean_dec(v___x_482_);
v___x_491_ = lean_nat_sub(v___x_490_, v_startInclusive_478_);
v___x_492_ = lean_unsigned_to_nat(10u);
v___x_493_ = lean_nat_mul(v_r_476_, v___x_492_);
lean_dec(v_r_476_);
v___x_494_ = lean_uint32_to_nat(v_c_483_);
v___x_495_ = lean_unsigned_to_nat(48u);
v___x_496_ = lean_nat_sub(v___x_494_, v___x_495_);
lean_dec(v___x_494_);
v___x_497_ = lean_nat_add(v___x_493_, v___x_496_);
lean_dec(v___x_496_);
lean_dec(v___x_493_);
v_it_475_ = v___x_491_;
v_r_476_ = v___x_497_;
goto _start;
}
}
}
else
{
lean_object* v___x_499_; 
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v_it_475_);
lean_ctor_set(v___x_499_, 1, v_r_476_);
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum___boxed(lean_object* v_pattern_500_, lean_object* v_it_501_, lean_object* v_r_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(v_pattern_500_, v_it_501_, v_r_502_);
lean_dec_ref(v_pattern_500_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux(lean_object* v_args_505_, lean_object* v_pattern_506_, lean_object* v_it_507_, lean_object* v_r_508_){
_start:
{
lean_object* v___x_509_; uint8_t v_decide_510_; 
v___x_509_ = lean_string_utf8_byte_size(v_pattern_506_);
v_decide_510_ = lean_nat_dec_eq(v_it_507_, v___x_509_);
if (v_decide_510_ == 0)
{
uint32_t v_c_511_; uint32_t v___x_512_; uint8_t v___x_513_; 
v_c_511_ = lean_string_utf8_get_fast(v_pattern_506_, v_it_507_);
v___x_512_ = 35;
v___x_513_ = lean_uint32_dec_eq(v_c_511_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_string_utf8_next_fast(v_pattern_506_, v_it_507_);
lean_dec(v_it_507_);
v___x_515_ = lean_string_push(v_r_508_, v_c_511_);
v_it_507_ = v___x_514_;
v_r_508_ = v___x_515_;
goto _start;
}
else
{
lean_object* v_it_u2081_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v_fst_521_; lean_object* v_snd_522_; lean_object* v___x_523_; lean_object* v_j_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v_it_u2081_517_ = lean_string_utf8_next_fast(v_pattern_506_, v_it_507_);
lean_dec(v_it_507_);
lean_inc_ref(v_pattern_506_);
v___x_518_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_518_, 0, v_pattern_506_);
lean_ctor_set(v___x_518_, 1, v_it_u2081_517_);
lean_ctor_set(v___x_518_, 2, v___x_509_);
v___x_519_ = lean_unsigned_to_nat(0u);
v___x_520_ = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(v___x_518_, v___x_519_, v___x_519_);
lean_dec_ref_known(v___x_518_, 3);
v_fst_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_fst_521_);
v_snd_522_ = lean_ctor_get(v___x_520_, 1);
lean_inc(v_snd_522_);
lean_dec_ref(v___x_520_);
v___x_523_ = lean_unsigned_to_nat(1u);
v_j_524_ = lean_nat_sub(v_snd_522_, v___x_523_);
lean_dec(v_snd_522_);
v___x_525_ = lean_nat_add(v_it_u2081_517_, v_fst_521_);
lean_dec(v_fst_521_);
v___x_526_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_527_ = l_List_getD___redArg(v_args_505_, v_j_524_, v___x_526_);
v___x_528_ = lean_string_append(v_r_508_, v___x_527_);
lean_dec(v___x_527_);
v_it_507_ = v___x_525_;
v_r_508_ = v___x_528_;
goto _start;
}
}
else
{
lean_dec(v_it_507_);
lean_dec_ref(v_pattern_506_);
return v_r_508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux___boxed(lean_object* v_args_530_, lean_object* v_pattern_531_, lean_object* v_it_532_, lean_object* v_r_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_expandExternPatternAux(v_args_530_, v_pattern_531_, v_it_532_, v_r_533_);
lean_dec(v_args_530_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter___redArg(lean_object* v_x_535_, lean_object* v_h__1_536_){
_start:
{
lean_object* v_fst_537_; lean_object* v_snd_538_; lean_object* v___x_539_; 
v_fst_537_ = lean_ctor_get(v_x_535_, 0);
lean_inc(v_fst_537_);
v_snd_538_ = lean_ctor_get(v_x_535_, 1);
lean_inc(v_snd_538_);
lean_dec_ref(v_x_535_);
v___x_539_ = lean_apply_2(v_h__1_536_, v_fst_537_, v_snd_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter(lean_object* v_pattern_540_, lean_object* v_it_u2081_541_, lean_object* v_motive_542_, lean_object* v_x_543_, lean_object* v_h__1_544_){
_start:
{
lean_object* v_fst_545_; lean_object* v_snd_546_; lean_object* v___x_547_; 
v_fst_545_ = lean_ctor_get(v_x_543_, 0);
lean_inc(v_fst_545_);
v_snd_546_ = lean_ctor_get(v_x_543_, 1);
lean_inc(v_snd_546_);
lean_dec_ref(v_x_543_);
v___x_547_ = lean_apply_2(v_h__1_544_, v_fst_545_, v_snd_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter___boxed(lean_object* v_pattern_548_, lean_object* v_it_u2081_549_, lean_object* v_motive_550_, lean_object* v_x_551_, lean_object* v_h__1_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter(v_pattern_548_, v_it_u2081_549_, v_motive_550_, v_x_551_, v_h__1_552_);
lean_dec(v_it_u2081_549_);
lean_dec_ref(v_pattern_548_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPattern(lean_object* v_pattern_554_, lean_object* v_args_555_){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_558_ = l_Lean_expandExternPatternAux(v_args_555_, v_pattern_554_, v___x_556_, v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPattern___boxed(lean_object* v_pattern_559_, lean_object* v_args_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_expandExternPattern(v_pattern_559_, v_args_560_);
lean_dec(v_args_560_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(lean_object* v_x_562_, lean_object* v_x_563_){
_start:
{
if (lean_obj_tag(v_x_563_) == 0)
{
return v_x_562_;
}
else
{
lean_object* v_head_564_; lean_object* v_tail_565_; lean_object* v___x_566_; 
v_head_564_ = lean_ctor_get(v_x_563_, 0);
v_tail_565_ = lean_ctor_get(v_x_563_, 1);
v___x_566_ = lean_string_append(v_x_562_, v_head_564_);
v_x_562_ = v___x_566_;
v_x_563_ = v_tail_565_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0___boxed(lean_object* v_x_568_, lean_object* v_x_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(v_x_568_, v_x_569_);
lean_dec(v_x_569_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleFnCall(lean_object* v_fn_574_, lean_object* v_args_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_576_ = ((lean_object*)(l_Lean_mkSimpleFnCall___closed__0));
v___x_577_ = lean_string_append(v_fn_574_, v___x_576_);
v___x_578_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_579_ = ((lean_object*)(l_Lean_mkSimpleFnCall___closed__1));
v___x_580_ = l_List_intersperseTR___redArg(v___x_579_, v_args_575_);
v___x_581_ = l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(v___x_578_, v___x_580_);
lean_dec(v___x_580_);
v___x_582_ = lean_string_append(v___x_577_, v___x_581_);
lean_dec_ref(v___x_581_);
v___x_583_ = ((lean_object*)(l_Lean_mkSimpleFnCall___closed__2));
v___x_584_ = lean_string_append(v___x_582_, v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend(lean_object* v_x_585_){
_start:
{
if (lean_obj_tag(v_x_585_) == 3)
{
lean_object* v___x_586_; 
v___x_586_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
return v___x_586_;
}
else
{
lean_object* v_backend_587_; 
v_backend_587_ = lean_ctor_get(v_x_585_, 0);
lean_inc(v_backend_587_);
return v_backend_587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend___boxed(lean_object* v_x_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_ExternEntry_backend(v_x_588_);
lean_dec(v_x_588_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(lean_object* v_backend_590_, lean_object* v_x_591_){
_start:
{
if (lean_obj_tag(v_x_591_) == 0)
{
lean_object* v___x_592_; 
v___x_592_ = lean_box(0);
return v___x_592_;
}
else
{
lean_object* v_head_593_; lean_object* v_tail_594_; lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v_head_593_ = lean_ctor_get(v_x_591_, 0);
v_tail_594_ = lean_ctor_get(v_x_591_, 1);
v___x_595_ = l_Lean_ExternEntry_backend(v_head_593_);
v___x_596_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
v___x_597_ = lean_name_eq(v___x_595_, v___x_596_);
if (v___x_597_ == 0)
{
uint8_t v___x_598_; 
v___x_598_ = lean_name_eq(v___x_595_, v_backend_590_);
lean_dec(v___x_595_);
if (v___x_598_ == 0)
{
v_x_591_ = v_tail_594_;
goto _start;
}
else
{
lean_object* v___x_600_; 
lean_inc(v_head_593_);
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v_head_593_);
return v___x_600_;
}
}
else
{
lean_object* v___x_601_; 
lean_dec(v___x_595_);
lean_inc(v_head_593_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v_head_593_);
return v___x_601_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0___boxed(lean_object* v_backend_602_, lean_object* v_x_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_602_, v_x_603_);
lean_dec(v_x_603_);
lean_dec(v_backend_602_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux(lean_object* v_backend_605_, lean_object* v_entries_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_605_, v_entries_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux___boxed(lean_object* v_backend_608_, lean_object* v_entries_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_getExternEntryForAux(v_backend_608_, v_entries_609_);
lean_dec(v_entries_609_);
lean_dec(v_backend_608_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor(lean_object* v_d_611_, lean_object* v_backend_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_612_, v_d_611_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor___boxed(lean_object* v_d_614_, lean_object* v_backend_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_getExternEntryFor(v_d_614_, v_backend_615_);
lean_dec(v_backend_615_);
lean_dec(v_d_614_);
return v_res_616_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExtern(lean_object* v_env_617_, lean_object* v_fn_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_getExternAttrData_x3f(v_env_617_, v_fn_618_);
if (lean_obj_tag(v___x_619_) == 0)
{
uint8_t v___x_620_; 
v___x_620_ = 0;
return v___x_620_;
}
else
{
uint8_t v___x_621_; 
lean_dec_ref_known(v___x_619_, 1);
v___x_621_ = 1;
return v___x_621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExtern___boxed(lean_object* v_env_622_, lean_object* v_fn_623_){
_start:
{
uint8_t v_res_624_; lean_object* v_r_625_; 
v_res_624_ = l_Lean_isExtern(v_env_622_, v_fn_623_);
v_r_625_ = lean_box(v_res_624_);
return v_r_625_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExternC(lean_object* v_env_626_, lean_object* v_fn_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_getExternAttrData_x3f(v_env_626_, v_fn_627_);
if (lean_obj_tag(v___x_628_) == 1)
{
lean_object* v_val_629_; 
v_val_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_val_629_);
lean_dec_ref_known(v___x_628_, 1);
if (lean_obj_tag(v_val_629_) == 1)
{
lean_object* v_head_630_; 
v_head_630_ = lean_ctor_get(v_val_629_, 0);
if (lean_obj_tag(v_head_630_) == 2)
{
lean_object* v_backend_631_; 
v_backend_631_ = lean_ctor_get(v_head_630_, 0);
lean_inc(v_backend_631_);
if (lean_obj_tag(v_backend_631_) == 1)
{
lean_object* v_pre_632_; 
v_pre_632_ = lean_ctor_get(v_backend_631_, 0);
if (lean_obj_tag(v_pre_632_) == 0)
{
lean_object* v_tail_633_; lean_object* v_str_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v_tail_633_ = lean_ctor_get(v_val_629_, 1);
lean_inc(v_tail_633_);
lean_dec_ref_known(v_val_629_, 2);
v_str_634_ = lean_ctor_get(v_backend_631_, 1);
lean_inc_ref(v_str_634_);
lean_dec_ref_known(v_backend_631_, 2);
v___x_635_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__2));
v___x_636_ = lean_string_dec_eq(v_str_634_, v___x_635_);
lean_dec_ref(v_str_634_);
if (v___x_636_ == 0)
{
lean_dec(v_tail_633_);
return v___x_636_;
}
else
{
if (lean_obj_tag(v_tail_633_) == 0)
{
return v___x_636_;
}
else
{
uint8_t v___x_637_; 
lean_dec(v_tail_633_);
v___x_637_ = 0;
return v___x_637_;
}
}
}
else
{
uint8_t v___x_638_; 
lean_dec_ref_known(v_backend_631_, 2);
lean_dec_ref_known(v_val_629_, 2);
v___x_638_ = 0;
return v___x_638_;
}
}
else
{
uint8_t v___x_639_; 
lean_dec(v_backend_631_);
lean_dec_ref_known(v_val_629_, 2);
v___x_639_ = 0;
return v___x_639_;
}
}
else
{
uint8_t v___x_640_; 
lean_dec_ref_known(v_val_629_, 2);
v___x_640_ = 0;
return v___x_640_;
}
}
else
{
uint8_t v___x_641_; 
lean_dec(v_val_629_);
v___x_641_ = 0;
return v___x_641_;
}
}
else
{
uint8_t v___x_642_; 
lean_dec(v___x_628_);
v___x_642_ = 0;
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExternC___boxed(lean_object* v_env_643_, lean_object* v_fn_644_){
_start:
{
uint8_t v_res_645_; lean_object* v_r_646_; 
v_res_645_ = l_Lean_isExternC(v_env_643_, v_fn_644_);
v_r_646_ = lean_box(v_res_645_);
return v_r_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternNameFor(lean_object* v_env_647_, lean_object* v_backend_648_, lean_object* v_fn_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_getExternAttrData_x3f(v_env_647_, v_fn_649_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v___x_651_; 
v___x_651_ = lean_box(0);
return v___x_651_;
}
else
{
lean_object* v_val_652_; lean_object* v___x_653_; 
v_val_652_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_val_652_);
lean_dec_ref_known(v___x_650_, 1);
v___x_653_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_648_, v_val_652_);
lean_dec(v_val_652_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v___x_654_; 
v___x_654_ = lean_box(0);
return v___x_654_;
}
else
{
lean_object* v_val_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_664_; 
v_val_655_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_664_ == 0)
{
v___x_657_ = v___x_653_;
v_isShared_658_ = v_isSharedCheck_664_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_val_655_);
lean_dec(v___x_653_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_664_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
if (lean_obj_tag(v_val_655_) == 2)
{
lean_object* v_fn_659_; lean_object* v___x_661_; 
v_fn_659_ = lean_ctor_get(v_val_655_, 1);
lean_inc_ref(v_fn_659_);
lean_dec_ref_known(v_val_655_, 2);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v_fn_659_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_fn_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
else
{
lean_object* v___x_663_; 
lean_del_object(v___x_657_);
lean_dec(v_val_655_);
v___x_663_ = lean_box(0);
return v___x_663_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExternNameFor___boxed(lean_object* v_env_665_, lean_object* v_backend_666_, lean_object* v_fn_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_getExternNameFor(v_env_665_, v_backend_666_, v_fn_667_);
lean_dec(v_backend_666_);
return v_res_668_;
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
