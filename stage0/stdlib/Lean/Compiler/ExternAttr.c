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
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_170_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_171_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1);
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
lean_ctor_set(v___x_173_, 2, v___x_172_);
lean_ctor_set(v___x_173_, 3, v___x_172_);
lean_ctor_set(v___x_173_, 4, v___x_171_);
lean_ctor_set(v___x_173_, 5, v___x_171_);
lean_ctor_set(v___x_173_, 6, v___x_171_);
lean_ctor_set(v___x_173_, 7, v___x_171_);
lean_ctor_set(v___x_173_, 8, v___x_171_);
lean_ctor_set(v___x_173_, 9, v___x_171_);
lean_ctor_set(v___x_173_, 10, v___x_171_);
lean_ctor_set(v___x_173_, 11, v___x_170_);
return v___x_173_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = lean_unsigned_to_nat(32u);
v___x_175_ = lean_mk_empty_array_with_capacity(v___x_174_);
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_177_ = ((size_t)5ULL);
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = lean_unsigned_to_nat(32u);
v___x_180_ = lean_mk_empty_array_with_capacity(v___x_179_);
v___x_181_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3);
v___x_182_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___x_180_);
lean_ctor_set(v___x_182_, 2, v___x_178_);
lean_ctor_set(v___x_182_, 3, v___x_178_);
lean_ctor_set_usize(v___x_182_, 4, v___x_177_);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_183_ = lean_box(1);
v___x_184_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4);
v___x_185_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1);
v___x_186_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v___x_184_);
lean_ctor_set(v___x_186_, 2, v___x_183_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1(lean_object* v_msgData_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v___x_191_; lean_object* v_toCold_192_; lean_object* v_env_193_; lean_object* v_options_194_; uint8_t v___x_195_; lean_object* v_env_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_191_ = lean_st_ref_get(v___y_189_);
v_toCold_192_ = lean_ctor_get(v___y_188_, 0);
v_env_193_ = lean_ctor_get(v___x_191_, 0);
lean_inc_ref(v_env_193_);
lean_dec(v___x_191_);
v_options_194_ = lean_ctor_get(v_toCold_192_, 2);
v___x_195_ = 0;
v_env_196_ = l_Lean_Environment_setRecordingDeps(v_env_193_, v___x_195_);
v___x_197_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2);
v___x_198_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_194_);
v___x_199_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_199_, 0, v_env_196_);
lean_ctor_set(v___x_199_, 1, v___x_197_);
lean_ctor_set(v___x_199_, 2, v___x_198_);
lean_ctor_set(v___x_199_, 3, v_options_194_);
v___x_200_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v_msgData_187_);
v___x_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1(v_msgData_202_, v___y_203_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(lean_object* v_msg_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_ref_211_; lean_object* v___x_212_; lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_221_; 
v_ref_211_ = lean_ctor_get(v___y_208_, 2);
v___x_212_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1(v_msg_207_, v___y_208_, v___y_209_);
v_a_213_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_221_ == 0)
{
v___x_215_ = v___x_212_;
v_isShared_216_ = v_isSharedCheck_221_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_212_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_221_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v___x_219_; 
lean_inc(v_ref_211_);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v_ref_211_);
lean_ctor_set(v___x_217_, 1, v_a_213_);
if (v_isShared_216_ == 0)
{
lean_ctor_set_tag(v___x_215_, 1);
lean_ctor_set(v___x_215_, 0, v___x_217_);
v___x_219_ = v___x_215_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg___boxed(lean_object* v_msg_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_222_, v___y_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(lean_object* v_ref_227_, lean_object* v_msg_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_toCold_232_; lean_object* v_currRecDepth_233_; lean_object* v_ref_234_; uint16_t v_optionFlags_235_; uint8_t v_suppressElabErrors_236_; uint8_t v_checkDeprecated_237_; uint8_t v_isRecordingDeps_238_; lean_object* v_ref_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_toCold_232_ = lean_ctor_get(v___y_229_, 0);
v_currRecDepth_233_ = lean_ctor_get(v___y_229_, 1);
v_ref_234_ = lean_ctor_get(v___y_229_, 2);
v_optionFlags_235_ = lean_ctor_get_uint16(v___y_229_, sizeof(void*)*3);
v_suppressElabErrors_236_ = lean_ctor_get_uint8(v___y_229_, sizeof(void*)*3 + 2);
v_checkDeprecated_237_ = lean_ctor_get_uint8(v___y_229_, sizeof(void*)*3 + 3);
v_isRecordingDeps_238_ = lean_ctor_get_uint8(v___y_229_, sizeof(void*)*3 + 4);
v_ref_239_ = l_Lean_replaceRef(v_ref_227_, v_ref_234_);
lean_inc(v_currRecDepth_233_);
lean_inc_ref(v_toCold_232_);
v___x_240_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_240_, 0, v_toCold_232_);
lean_ctor_set(v___x_240_, 1, v_currRecDepth_233_);
lean_ctor_set(v___x_240_, 2, v_ref_239_);
lean_ctor_set_uint16(v___x_240_, sizeof(void*)*3, v_optionFlags_235_);
lean_ctor_set_uint8(v___x_240_, sizeof(void*)*3 + 2, v_suppressElabErrors_236_);
lean_ctor_set_uint8(v___x_240_, sizeof(void*)*3 + 3, v_checkDeprecated_237_);
lean_ctor_set_uint8(v___x_240_, sizeof(void*)*3 + 4, v_isRecordingDeps_238_);
v___x_241_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_228_, v___x_240_, v___y_230_);
lean_dec_ref_known(v___x_240_, 3);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg___boxed(lean_object* v_ref_242_, lean_object* v_msg_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v_ref_242_, v_msg_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v_ref_242_);
return v_res_247_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__0));
v___x_250_ = l_Lean_stringToMessageData(v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(lean_object* v_as_254_, size_t v_sz_255_, size_t v_i_256_, lean_object* v_b_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_a_262_; uint8_t v___x_266_; 
v___x_266_ = lean_usize_dec_lt(v_i_256_, v_sz_255_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v_b_257_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v_a_270_; lean_object* v___y_272_; lean_object* v_str_273_; lean_object* v___y_281_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_unsigned_to_nat(0u);
v_a_270_ = lean_array_uget_borrowed(v_as_254_, v_i_256_);
v___x_297_ = l_Lean_Syntax_getArg(v_a_270_, v___x_269_);
v___x_298_ = l_Lean_Syntax_isNone(v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = l_Lean_Syntax_getArg(v___x_297_, v___x_269_);
lean_dec(v___x_297_);
v___x_300_ = l_Lean_Syntax_getId(v___x_299_);
lean_dec(v___x_299_);
v___y_281_ = v___x_300_;
goto v___jp_280_;
}
else
{
lean_object* v___x_301_; 
lean_dec(v___x_297_);
v___x_301_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
v___y_281_ = v___x_301_;
goto v___jp_280_;
}
v___jp_271_:
{
lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = l_Lean_Syntax_getArg(v_a_270_, v___x_268_);
v___x_275_ = l_Lean_Syntax_isNone(v___x_274_);
lean_dec(v___x_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_276_, 0, v___y_272_);
lean_ctor_set(v___x_276_, 1, v_str_273_);
v___x_277_ = lean_array_push(v_b_257_, v___x_276_);
v_a_262_ = v___x_277_;
goto v___jp_261_;
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_278_, 0, v___y_272_);
lean_ctor_set(v___x_278_, 1, v_str_273_);
v___x_279_ = lean_array_push(v_b_257_, v___x_278_);
v_a_262_ = v___x_279_;
goto v___jp_261_;
}
}
v___jp_280_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = lean_unsigned_to_nat(2u);
v___x_283_ = l_Lean_Syntax_getArg(v_a_270_, v___x_282_);
v___x_284_ = l_Lean_Syntax_isStrLit_x3f(v___x_283_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1);
v___x_286_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v___x_283_, v___x_285_, v___y_258_, v___y_259_);
lean_dec(v___x_283_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_a_287_);
lean_dec_ref_known(v___x_286_, 1);
v___y_272_ = v___y_281_;
v_str_273_ = v_a_287_;
goto v___jp_271_;
}
else
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
lean_dec(v___y_281_);
lean_dec_ref(v_b_257_);
v_a_288_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v___x_286_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_286_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
else
{
lean_object* v_val_296_; 
lean_dec(v___x_283_);
v_val_296_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_val_296_);
lean_dec_ref_known(v___x_284_, 1);
v___y_272_ = v___y_281_;
v_str_273_ = v_val_296_;
goto v___jp_271_;
}
}
}
v___jp_261_:
{
size_t v___x_263_; size_t v___x_264_; 
v___x_263_ = ((size_t)1ULL);
v___x_264_ = lean_usize_add(v_i_256_, v___x_263_);
v_i_256_ = v___x_264_;
v_b_257_ = v_a_262_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___boxed(lean_object* v_as_302_, lean_object* v_sz_303_, lean_object* v_i_304_, lean_object* v_b_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
size_t v_sz_boxed_309_; size_t v_i_boxed_310_; lean_object* v_res_311_; 
v_sz_boxed_309_ = lean_unbox_usize(v_sz_303_);
lean_dec(v_sz_303_);
v_i_boxed_310_ = lean_unbox_usize(v_i_304_);
lean_dec(v_i_304_);
v_res_311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(v_as_302_, v_sz_boxed_309_, v_i_boxed_310_, v_b_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec_ref(v_as_302_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(lean_object* v_stx_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v_entriesStx_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_323_ = lean_unsigned_to_nat(1u);
v___x_324_ = l_Lean_Syntax_getArg(v_stx_319_, v___x_323_);
v_entriesStx_325_ = l_Lean_Syntax_getArgs(v___x_324_);
lean_dec(v___x_324_);
v___x_326_ = lean_array_get_size(v_entriesStx_325_);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_nat_dec_eq(v___x_326_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v_entries_329_; size_t v_sz_330_; size_t v___x_331_; lean_object* v___x_332_; 
v_entries_329_ = ((lean_object*)(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__0));
v_sz_330_ = lean_array_size(v_entriesStx_325_);
v___x_331_ = ((size_t)0ULL);
v___x_332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(v_entriesStx_325_, v_sz_330_, v___x_331_, v_entries_329_, v_a_320_, v_a_321_);
lean_dec_ref(v_entriesStx_325_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_341_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_341_ == 0)
{
v___x_335_ = v___x_332_;
v_isShared_336_ = v_isSharedCheck_341_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_332_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_341_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_337_ = lean_array_to_list(v_a_333_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_337_);
v___x_339_ = v___x_335_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
else
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
v_a_342_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_332_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_332_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; 
lean_dec_ref(v_entriesStx_325_);
v___x_350_ = ((lean_object*)(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2));
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___boxed(lean_object* v_stx_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(v_stx_352_, v_a_353_, v_a_354_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec(v_stx_352_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(lean_object* v_00_u03b1_357_, lean_object* v_ref_358_, lean_object* v_msg_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v_ref_358_, v_msg_359_, v___y_360_, v___y_361_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___boxed(lean_object* v_00_u03b1_364_, lean_object* v_ref_365_, lean_object* v_msg_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(v_00_u03b1_364_, v_ref_365_, v_msg_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v_ref_365_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0(lean_object* v_00_u03b1_371_, lean_object* v_msg_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_372_, v___y_373_, v___y_374_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___boxed(lean_object* v_00_u03b1_377_, lean_object* v_msg_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0(v_00_u03b1_377_, v_msg_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(lean_object* v_x_383_, lean_object* v_stx_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(v_stx_384_, v___y_385_, v___y_386_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v_x_389_, lean_object* v_stx_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v_x_389_, v_stx_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v_stx_390_);
lean_dec(v_x_389_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(lean_object* v_declName_395_, lean_object* v_externAttrData_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
uint8_t v___y_401_; lean_object* v___x_406_; lean_object* v_env_407_; uint8_t v___x_422_; 
v___x_406_ = lean_st_ref_get(v___y_398_);
v_env_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc_ref_n(v_env_407_, 2);
lean_dec(v___x_406_);
lean_inc(v_declName_395_);
v___x_422_ = l_Lean_Environment_isProjectionFn(v_env_407_, v_declName_395_);
if (v___x_422_ == 0)
{
uint8_t v___x_423_; 
lean_inc(v_declName_395_);
lean_inc_ref(v_env_407_);
v___x_423_ = l_Lean_Environment_isConstructor(v_env_407_, v_declName_395_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec_ref(v_env_407_);
lean_dec(v_declName_395_);
v___x_424_ = lean_box(0);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
else
{
goto v___jp_408_;
}
}
else
{
goto v___jp_408_;
}
v___jp_400_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_402_ = lean_unsigned_to_nat(1u);
v___x_403_ = lean_mk_empty_array_with_capacity(v___x_402_);
v___x_404_ = lean_array_push(v___x_403_, v_declName_395_);
v___x_405_ = l_Lean_compileDecls(v___x_404_, v___y_401_, v___y_397_, v___y_398_);
return v___x_405_;
}
v___jp_408_:
{
uint8_t v___x_409_; uint8_t v___x_410_; lean_object* v___x_411_; 
v___x_409_ = 1;
v___x_410_ = 0;
lean_inc(v_declName_395_);
v___x_411_ = l_Lean_Environment_find_x3f(v_env_407_, v_declName_395_, v___x_410_);
if (lean_obj_tag(v___x_411_) == 1)
{
lean_object* v_val_412_; 
v_val_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_val_412_);
lean_dec_ref_known(v___x_411_, 1);
if (lean_obj_tag(v_val_412_) == 2)
{
lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_420_; 
lean_dec(v_declName_395_);
v_isSharedCheck_420_ = !lean_is_exclusive(v_val_412_);
if (v_isSharedCheck_420_ == 0)
{
lean_object* v_unused_421_; 
v_unused_421_ = lean_ctor_get(v_val_412_, 0);
lean_dec(v_unused_421_);
v___x_414_ = v_val_412_;
v_isShared_415_ = v_isSharedCheck_420_;
goto v_resetjp_413_;
}
else
{
lean_dec(v_val_412_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_420_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_416_ = lean_box(0);
if (v_isShared_415_ == 0)
{
lean_ctor_set_tag(v___x_414_, 0);
lean_ctor_set(v___x_414_, 0, v___x_416_);
v___x_418_ = v___x_414_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
else
{
lean_dec(v_val_412_);
v___y_401_ = v___x_409_;
goto v___jp_400_;
}
}
else
{
lean_dec(v___x_411_);
v___y_401_ = v___x_409_;
goto v___jp_400_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v_declName_426_, lean_object* v_externAttrData_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v_declName_426_, v_externAttrData_427_, v___y_428_, v___y_429_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v_externAttrData_427_);
return v_res_431_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(uint8_t v___x_432_, lean_object* v_env_433_, lean_object* v_n_434_, lean_object* v_x_435_){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = l_Lean_Environment_contains(v_env_433_, v_n_434_, v___x_432_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v___x_437_, lean_object* v_env_438_, lean_object* v_n_439_, lean_object* v_x_440_){
_start:
{
uint8_t v___x_580__boxed_441_; uint8_t v_res_442_; lean_object* v_r_443_; 
v___x_580__boxed_441_ = lean_unbox(v___x_437_);
v_res_442_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v___x_580__boxed_441_, v_env_438_, v_n_439_, v_x_440_);
lean_dec(v_x_440_);
v_r_443_ = lean_box(v_res_442_);
return v_r_443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = ((lean_object*)(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_));
v___x_471_ = l_Lean_registerParametricAttribute___redArg(v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(lean_object* v_a_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_();
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternAttrData_x3f(lean_object* v_env_474_, lean_object* v_n_475_){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = lean_box(0);
v___x_477_ = l_Lean_externAttr;
v___x_478_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_476_, v___x_477_, v_env_474_, v_n_475_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(lean_object* v_pattern_479_, lean_object* v_it_480_, lean_object* v_r_481_){
_start:
{
lean_object* v_str_482_; lean_object* v_startInclusive_483_; lean_object* v_endExclusive_484_; lean_object* v___x_485_; uint8_t v_decide_486_; 
v_str_482_ = lean_ctor_get(v_pattern_479_, 0);
v_startInclusive_483_ = lean_ctor_get(v_pattern_479_, 1);
v_endExclusive_484_ = lean_ctor_get(v_pattern_479_, 2);
v___x_485_ = lean_nat_sub(v_endExclusive_484_, v_startInclusive_483_);
v_decide_486_ = lean_nat_dec_eq(v_it_480_, v___x_485_);
lean_dec(v___x_485_);
if (v_decide_486_ == 0)
{
lean_object* v___x_487_; uint32_t v_c_488_; uint32_t v___x_489_; uint8_t v___x_490_; 
v___x_487_ = lean_nat_add(v_startInclusive_483_, v_it_480_);
v_c_488_ = lean_string_utf8_get_fast(v_str_482_, v___x_487_);
v___x_489_ = 48;
v___x_490_ = lean_uint32_dec_le(v___x_489_, v_c_488_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; 
lean_dec(v___x_487_);
v___x_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_491_, 0, v_it_480_);
lean_ctor_set(v___x_491_, 1, v_r_481_);
return v___x_491_;
}
else
{
uint32_t v___x_492_; uint8_t v___x_493_; 
v___x_492_ = 57;
v___x_493_ = lean_uint32_dec_le(v_c_488_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; 
lean_dec(v___x_487_);
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v_it_480_);
lean_ctor_set(v___x_494_, 1, v_r_481_);
return v___x_494_;
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
lean_dec(v_it_480_);
v___x_495_ = lean_string_utf8_next_fast(v_str_482_, v___x_487_);
lean_dec(v___x_487_);
v___x_496_ = lean_nat_sub(v___x_495_, v_startInclusive_483_);
v___x_497_ = lean_unsigned_to_nat(10u);
v___x_498_ = lean_nat_mul(v_r_481_, v___x_497_);
lean_dec(v_r_481_);
v___x_499_ = lean_uint32_to_nat(v_c_488_);
v___x_500_ = lean_unsigned_to_nat(48u);
v___x_501_ = lean_nat_sub(v___x_499_, v___x_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_nat_add(v___x_498_, v___x_501_);
lean_dec(v___x_501_);
lean_dec(v___x_498_);
v_it_480_ = v___x_496_;
v_r_481_ = v___x_502_;
goto _start;
}
}
}
else
{
lean_object* v___x_504_; 
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v_it_480_);
lean_ctor_set(v___x_504_, 1, v_r_481_);
return v___x_504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum___boxed(lean_object* v_pattern_505_, lean_object* v_it_506_, lean_object* v_r_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(v_pattern_505_, v_it_506_, v_r_507_);
lean_dec_ref(v_pattern_505_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux(lean_object* v_args_510_, lean_object* v_pattern_511_, lean_object* v_it_512_, lean_object* v_r_513_){
_start:
{
lean_object* v___x_514_; uint8_t v_decide_515_; 
v___x_514_ = lean_string_utf8_byte_size(v_pattern_511_);
v_decide_515_ = lean_nat_dec_eq(v_it_512_, v___x_514_);
if (v_decide_515_ == 0)
{
uint32_t v_c_516_; uint32_t v___x_517_; uint8_t v___x_518_; 
v_c_516_ = lean_string_utf8_get_fast(v_pattern_511_, v_it_512_);
v___x_517_ = 35;
v___x_518_ = lean_uint32_dec_eq(v_c_516_, v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_string_utf8_next_fast(v_pattern_511_, v_it_512_);
lean_dec(v_it_512_);
v___x_520_ = lean_string_push(v_r_513_, v_c_516_);
v_it_512_ = v___x_519_;
v_r_513_ = v___x_520_;
goto _start;
}
else
{
lean_object* v_it_u2081_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v_fst_526_; lean_object* v_snd_527_; lean_object* v___x_528_; lean_object* v_j_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v_it_u2081_522_ = lean_string_utf8_next_fast(v_pattern_511_, v_it_512_);
lean_dec(v_it_512_);
lean_inc_ref(v_pattern_511_);
v___x_523_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_523_, 0, v_pattern_511_);
lean_ctor_set(v___x_523_, 1, v_it_u2081_522_);
lean_ctor_set(v___x_523_, 2, v___x_514_);
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(v___x_523_, v___x_524_, v___x_524_);
lean_dec_ref_known(v___x_523_, 3);
v_fst_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_fst_526_);
v_snd_527_ = lean_ctor_get(v___x_525_, 1);
lean_inc(v_snd_527_);
lean_dec_ref(v___x_525_);
v___x_528_ = lean_unsigned_to_nat(1u);
v_j_529_ = lean_nat_sub(v_snd_527_, v___x_528_);
lean_dec(v_snd_527_);
v___x_530_ = lean_nat_add(v_it_u2081_522_, v_fst_526_);
lean_dec(v_fst_526_);
v___x_531_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_532_ = l_List_getD___redArg(v_args_510_, v_j_529_, v___x_531_);
v___x_533_ = lean_string_append(v_r_513_, v___x_532_);
lean_dec(v___x_532_);
v_it_512_ = v___x_530_;
v_r_513_ = v___x_533_;
goto _start;
}
}
else
{
lean_dec(v_it_512_);
lean_dec_ref(v_pattern_511_);
return v_r_513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux___boxed(lean_object* v_args_535_, lean_object* v_pattern_536_, lean_object* v_it_537_, lean_object* v_r_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_expandExternPatternAux(v_args_535_, v_pattern_536_, v_it_537_, v_r_538_);
lean_dec(v_args_535_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter___redArg(lean_object* v_x_540_, lean_object* v_h__1_541_){
_start:
{
lean_object* v_fst_542_; lean_object* v_snd_543_; lean_object* v___x_544_; 
v_fst_542_ = lean_ctor_get(v_x_540_, 0);
lean_inc(v_fst_542_);
v_snd_543_ = lean_ctor_get(v_x_540_, 1);
lean_inc(v_snd_543_);
lean_dec_ref(v_x_540_);
v___x_544_ = lean_apply_2(v_h__1_541_, v_fst_542_, v_snd_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter(lean_object* v_pattern_545_, lean_object* v_it_u2081_546_, lean_object* v_motive_547_, lean_object* v_x_548_, lean_object* v_h__1_549_){
_start:
{
lean_object* v_fst_550_; lean_object* v_snd_551_; lean_object* v___x_552_; 
v_fst_550_ = lean_ctor_get(v_x_548_, 0);
lean_inc(v_fst_550_);
v_snd_551_ = lean_ctor_get(v_x_548_, 1);
lean_inc(v_snd_551_);
lean_dec_ref(v_x_548_);
v___x_552_ = lean_apply_2(v_h__1_549_, v_fst_550_, v_snd_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter___boxed(lean_object* v_pattern_553_, lean_object* v_it_u2081_554_, lean_object* v_motive_555_, lean_object* v_x_556_, lean_object* v_h__1_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter(v_pattern_553_, v_it_u2081_554_, v_motive_555_, v_x_556_, v_h__1_557_);
lean_dec(v_it_u2081_554_);
lean_dec_ref(v_pattern_553_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPattern(lean_object* v_pattern_559_, lean_object* v_args_560_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_563_ = l_Lean_expandExternPatternAux(v_args_560_, v_pattern_559_, v___x_561_, v___x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPattern___boxed(lean_object* v_pattern_564_, lean_object* v_args_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_expandExternPattern(v_pattern_564_, v_args_565_);
lean_dec(v_args_565_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(lean_object* v_x_567_, lean_object* v_x_568_){
_start:
{
if (lean_obj_tag(v_x_568_) == 0)
{
return v_x_567_;
}
else
{
lean_object* v_head_569_; lean_object* v_tail_570_; lean_object* v___x_571_; 
v_head_569_ = lean_ctor_get(v_x_568_, 0);
v_tail_570_ = lean_ctor_get(v_x_568_, 1);
v___x_571_ = lean_string_append(v_x_567_, v_head_569_);
v_x_567_ = v___x_571_;
v_x_568_ = v_tail_570_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0___boxed(lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(v_x_573_, v_x_574_);
lean_dec(v_x_574_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleFnCall(lean_object* v_fn_579_, lean_object* v_args_580_){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_581_ = ((lean_object*)(l_Lean_mkSimpleFnCall___closed__0));
v___x_582_ = lean_string_append(v_fn_579_, v___x_581_);
v___x_583_ = ((lean_object*)(l_Lean_expandExternPatternAux___closed__0));
v___x_584_ = ((lean_object*)(l_Lean_mkSimpleFnCall___closed__1));
v___x_585_ = l_List_intersperseTR___redArg(v___x_584_, v_args_580_);
v___x_586_ = l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(v___x_583_, v___x_585_);
lean_dec(v___x_585_);
v___x_587_ = lean_string_append(v___x_582_, v___x_586_);
lean_dec_ref(v___x_586_);
v___x_588_ = ((lean_object*)(l_Lean_mkSimpleFnCall___closed__2));
v___x_589_ = lean_string_append(v___x_587_, v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend(lean_object* v_x_590_){
_start:
{
if (lean_obj_tag(v_x_590_) == 3)
{
lean_object* v___x_591_; 
v___x_591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
return v___x_591_;
}
else
{
lean_object* v_backend_592_; 
v_backend_592_ = lean_ctor_get(v_x_590_, 0);
lean_inc(v_backend_592_);
return v_backend_592_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend___boxed(lean_object* v_x_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_ExternEntry_backend(v_x_593_);
lean_dec(v_x_593_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(lean_object* v_backend_595_, lean_object* v_x_596_){
_start:
{
if (lean_obj_tag(v_x_596_) == 0)
{
lean_object* v___x_597_; 
v___x_597_ = lean_box(0);
return v___x_597_;
}
else
{
lean_object* v_head_598_; lean_object* v_tail_599_; lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v_head_598_ = lean_ctor_get(v_x_596_, 0);
v_tail_599_ = lean_ctor_get(v_x_596_, 1);
v___x_600_ = l_Lean_ExternEntry_backend(v_head_598_);
v___x_601_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3));
v___x_602_ = lean_name_eq(v___x_600_, v___x_601_);
if (v___x_602_ == 0)
{
uint8_t v___x_603_; 
v___x_603_ = lean_name_eq(v___x_600_, v_backend_595_);
lean_dec(v___x_600_);
if (v___x_603_ == 0)
{
v_x_596_ = v_tail_599_;
goto _start;
}
else
{
lean_object* v___x_605_; 
lean_inc(v_head_598_);
v___x_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_605_, 0, v_head_598_);
return v___x_605_;
}
}
else
{
lean_object* v___x_606_; 
lean_dec(v___x_600_);
lean_inc(v_head_598_);
v___x_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_606_, 0, v_head_598_);
return v___x_606_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0___boxed(lean_object* v_backend_607_, lean_object* v_x_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_607_, v_x_608_);
lean_dec(v_x_608_);
lean_dec(v_backend_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux(lean_object* v_backend_610_, lean_object* v_entries_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_610_, v_entries_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux___boxed(lean_object* v_backend_613_, lean_object* v_entries_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_getExternEntryForAux(v_backend_613_, v_entries_614_);
lean_dec(v_entries_614_);
lean_dec(v_backend_613_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor(lean_object* v_d_616_, lean_object* v_backend_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_617_, v_d_616_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor___boxed(lean_object* v_d_619_, lean_object* v_backend_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_getExternEntryFor(v_d_619_, v_backend_620_);
lean_dec(v_backend_620_);
lean_dec(v_d_619_);
return v_res_621_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExtern(lean_object* v_env_622_, lean_object* v_fn_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_getExternAttrData_x3f(v_env_622_, v_fn_623_);
if (lean_obj_tag(v___x_624_) == 0)
{
uint8_t v___x_625_; 
v___x_625_ = 0;
return v___x_625_;
}
else
{
uint8_t v___x_626_; 
lean_dec_ref_known(v___x_624_, 1);
v___x_626_ = 1;
return v___x_626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExtern___boxed(lean_object* v_env_627_, lean_object* v_fn_628_){
_start:
{
uint8_t v_res_629_; lean_object* v_r_630_; 
v_res_629_ = l_Lean_isExtern(v_env_627_, v_fn_628_);
v_r_630_ = lean_box(v_res_629_);
return v_r_630_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExternC(lean_object* v_env_631_, lean_object* v_fn_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_getExternAttrData_x3f(v_env_631_, v_fn_632_);
if (lean_obj_tag(v___x_633_) == 1)
{
lean_object* v_val_634_; 
v_val_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_val_634_);
lean_dec_ref_known(v___x_633_, 1);
if (lean_obj_tag(v_val_634_) == 1)
{
lean_object* v_head_635_; 
v_head_635_ = lean_ctor_get(v_val_634_, 0);
if (lean_obj_tag(v_head_635_) == 2)
{
lean_object* v_backend_636_; 
v_backend_636_ = lean_ctor_get(v_head_635_, 0);
lean_inc(v_backend_636_);
if (lean_obj_tag(v_backend_636_) == 1)
{
lean_object* v_pre_637_; 
v_pre_637_ = lean_ctor_get(v_backend_636_, 0);
if (lean_obj_tag(v_pre_637_) == 0)
{
lean_object* v_tail_638_; lean_object* v_str_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_tail_638_ = lean_ctor_get(v_val_634_, 1);
lean_inc(v_tail_638_);
lean_dec_ref_known(v_val_634_, 2);
v_str_639_ = lean_ctor_get(v_backend_636_, 1);
lean_inc_ref(v_str_639_);
lean_dec_ref_known(v_backend_636_, 2);
v___x_640_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__2));
v___x_641_ = lean_string_dec_eq(v_str_639_, v___x_640_);
lean_dec_ref(v_str_639_);
if (v___x_641_ == 0)
{
lean_dec(v_tail_638_);
return v___x_641_;
}
else
{
if (lean_obj_tag(v_tail_638_) == 0)
{
return v___x_641_;
}
else
{
uint8_t v___x_642_; 
lean_dec(v_tail_638_);
v___x_642_ = 0;
return v___x_642_;
}
}
}
else
{
uint8_t v___x_643_; 
lean_dec_ref_known(v_backend_636_, 2);
lean_dec_ref_known(v_val_634_, 2);
v___x_643_ = 0;
return v___x_643_;
}
}
else
{
uint8_t v___x_644_; 
lean_dec(v_backend_636_);
lean_dec_ref_known(v_val_634_, 2);
v___x_644_ = 0;
return v___x_644_;
}
}
else
{
uint8_t v___x_645_; 
lean_dec_ref_known(v_val_634_, 2);
v___x_645_ = 0;
return v___x_645_;
}
}
else
{
uint8_t v___x_646_; 
lean_dec(v_val_634_);
v___x_646_ = 0;
return v___x_646_;
}
}
else
{
uint8_t v___x_647_; 
lean_dec(v___x_633_);
v___x_647_ = 0;
return v___x_647_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExternC___boxed(lean_object* v_env_648_, lean_object* v_fn_649_){
_start:
{
uint8_t v_res_650_; lean_object* v_r_651_; 
v_res_650_ = l_Lean_isExternC(v_env_648_, v_fn_649_);
v_r_651_ = lean_box(v_res_650_);
return v_r_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternNameFor(lean_object* v_env_652_, lean_object* v_backend_653_, lean_object* v_fn_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_getExternAttrData_x3f(v_env_652_, v_fn_654_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v___x_656_; 
v___x_656_ = lean_box(0);
return v___x_656_;
}
else
{
lean_object* v_val_657_; lean_object* v___x_658_; 
v_val_657_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_val_657_);
lean_dec_ref_known(v___x_655_, 1);
v___x_658_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_653_, v_val_657_);
lean_dec(v_val_657_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v___x_659_; 
v___x_659_ = lean_box(0);
return v___x_659_;
}
else
{
lean_object* v_val_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_669_; 
v_val_660_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_669_ == 0)
{
v___x_662_ = v___x_658_;
v_isShared_663_ = v_isSharedCheck_669_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_val_660_);
lean_dec(v___x_658_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_669_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
if (lean_obj_tag(v_val_660_) == 2)
{
lean_object* v_fn_664_; lean_object* v___x_666_; 
v_fn_664_ = lean_ctor_get(v_val_660_, 1);
lean_inc_ref(v_fn_664_);
lean_dec_ref_known(v_val_660_, 2);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v_fn_664_);
v___x_666_ = v___x_662_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_fn_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
else
{
lean_object* v___x_668_; 
lean_del_object(v___x_662_);
lean_dec(v_val_660_);
v___x_668_ = lean_box(0);
return v___x_668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExternNameFor___boxed(lean_object* v_env_670_, lean_object* v_backend_671_, lean_object* v_fn_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_getExternNameFor(v_env_670_, v_backend_671_, v_fn_672_);
lean_dec(v_backend_671_);
return v_res_673_;
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
