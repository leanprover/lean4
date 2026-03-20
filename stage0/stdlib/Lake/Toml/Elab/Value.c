// Lean compiler output
// Module: Lake.Toml.Elab.Value
// Imports: public import Lake.Toml.Data.Value public import Lake.Toml.Grammar meta import all Lake.Toml.Grammar
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_substring_tostring(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_String_Slice_positions(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_sub(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_instInhabitedSlice;
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Substring_Raw_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isLit_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lake_Toml_RBDict_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_push___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lake_Toml_RBDict_findEntry_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lake_Toml_DateTime_ofString_x3f(lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Int_negOfNat(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
double lean_float_negate(double);
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
extern lean_object* l_Lean_Core_instMonadRefCoreM;
extern lean_object* l_Lean_Core_instAddMessageContextCoreM;
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_empty(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1;
static const lean_closure_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2_value;
static const lean_closure_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ill-formed "};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Toml"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "boolean"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__2_value),LEAN_SCALAR_PTR_LITERAL(76, 74, 28, 167, 158, 175, 30, 0)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "invalid boolean"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__4 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__4_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__6 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__6_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__6_value),LEAN_SCALAR_PTR_LITERAL(94, 186, 129, 3, 94, 77, 39, 82)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__8 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__8_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__8_value),LEAN_SCALAR_PTR_LITERAL(45, 94, 147, 128, 103, 18, 162, 55)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeSign(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decInt"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 5, 249, 175, 125, 238, 54, 100)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "ill-formed decimal integer syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1;
static const lean_array_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inf"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nan"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2;
LEAN_EXPORT double l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___boxed(lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "float"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(104, 154, 151, 104, 68, 255, 246, 246)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "ill-formed float syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "binNum"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 60, 170, 39, 77, 137, 193, 6)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "ill-formed binary number syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "octNum"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 70, 221, 168, 145, 119, 144, 197)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ill-formed octal number syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(uint32_t);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexNum"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 174, 95, 211, 123, 63, 171, 252)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "ill-formed hexadecimal number syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "invalid date-time"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dateTime"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__2_value),LEAN_SCALAR_PTR_LITERAL(100, 234, 1, 129, 172, 254, 231, 202)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "ill-formed date-time syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__4 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__4_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__4_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__5 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__5_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "literalString"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 168, 165, 209, 230, 255, 154, 83)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "ill-formed literalString syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "invalid unicode escape `"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "basicString"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__1_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__1_value),LEAN_SCALAR_PTR_LITERAL(164, 34, 208, 112, 75, 114, 213, 233)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ill-formed basic string syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__3_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__3_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__4 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__4_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "mlLiteralString"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 215, 18, 247, 52, 33, 2, 54)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "ill-formed multi-line literal string syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mlBasicString"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 27, 188, 79, 217, 46, 221, 25)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "ill-formed multi-line basic string syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "string"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 134, 223, 178, 21, 25, 142, 203)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "ill-formed string syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__2_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unquotedKey"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 43, 232, 206, 44, 188, 39, 241)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ill-formed unquoted key syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_elabSimpleKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpleKey"};
static const lean_object* l_Lake_Toml_elabSimpleKey___closed__0 = (const lean_object*)&l_Lake_Toml_elabSimpleKey___closed__0_value;
static const lean_ctor_object l_Lake_Toml_elabSimpleKey___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_elabSimpleKey___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_elabSimpleKey___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_elabSimpleKey___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_elabSimpleKey___closed__1_value_aux_1),((lean_object*)&l_Lake_Toml_elabSimpleKey___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 51, 117, 190, 121, 223, 170, 220)}};
static const lean_object* l_Lake_Toml_elabSimpleKey___closed__1 = (const lean_object*)&l_Lake_Toml_elabSimpleKey___closed__1_value;
static const lean_string_object l_Lake_Toml_elabSimpleKey___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "ill-formed simple key syntax"};
static const lean_object* l_Lake_Toml_elabSimpleKey___closed__2 = (const lean_object*)&l_Lake_Toml_elabSimpleKey___closed__2_value;
static lean_once_cell_t l_Lake_Toml_elabSimpleKey___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_elabSimpleKey___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "array"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 212, 239, 77, 14, 34, 57, 134)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "ill-formed array syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__2_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "cannot redefine key `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "keyval"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 46, 78, 232, 161, 211, 209, 25)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "ill-formed key-value pair syntax"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "key"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__4_value),LEAN_SCALAR_PTR_LITERAL(44, 24, 166, 18, 184, 133, 165, 53)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "ill-formed key syntax"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "inlineTable"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 125, 46, 131, 161, 142, 50, 23)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ill-formed inline table syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__2_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_elabVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "ill-formed value syntax"};
static const lean_object* l_Lake_Toml_elabVal___closed__0 = (const lean_object*)&l_Lake_Toml_elabVal___closed__0_value;
static lean_once_cell_t l_Lake_Toml_elabVal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_elabVal___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0);
v___x_3_ = l_ReaderT_instMonad___redArg(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit(lean_object* v_k_8_, lean_object* v_x_9_, lean_object* v_name_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; lean_object* v_toApplicative_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_64_; 
v___x_14_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1);
v_toApplicative_15_ = lean_ctor_get(v___x_14_, 0);
v_isSharedCheck_64_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_64_ == 0)
{
lean_object* v_unused_65_; 
v_unused_65_ = lean_ctor_get(v___x_14_, 1);
lean_dec(v_unused_65_);
v___x_17_ = v___x_14_;
v_isShared_18_ = v_isSharedCheck_64_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_toApplicative_15_);
lean_dec(v___x_14_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_64_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v_toFunctor_19_; lean_object* v_toSeq_20_; lean_object* v_toSeqLeft_21_; lean_object* v_toSeqRight_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_62_; 
v_toFunctor_19_ = lean_ctor_get(v_toApplicative_15_, 0);
v_toSeq_20_ = lean_ctor_get(v_toApplicative_15_, 2);
v_toSeqLeft_21_ = lean_ctor_get(v_toApplicative_15_, 3);
v_toSeqRight_22_ = lean_ctor_get(v_toApplicative_15_, 4);
v_isSharedCheck_62_ = !lean_is_exclusive(v_toApplicative_15_);
if (v_isSharedCheck_62_ == 0)
{
lean_object* v_unused_63_; 
v_unused_63_ = lean_ctor_get(v_toApplicative_15_, 1);
lean_dec(v_unused_63_);
v___x_24_ = v_toApplicative_15_;
v_isShared_25_ = v_isSharedCheck_62_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_toSeqRight_22_);
lean_inc(v_toSeqLeft_21_);
lean_inc(v_toSeq_20_);
lean_inc(v_toFunctor_19_);
lean_dec(v_toApplicative_15_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_62_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___f_26_; lean_object* v___f_27_; lean_object* v___f_28_; lean_object* v___f_29_; lean_object* v___x_30_; lean_object* v___f_31_; lean_object* v___f_32_; lean_object* v___f_33_; lean_object* v___x_35_; 
v___f_26_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2));
v___f_27_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3));
lean_inc_ref(v_toFunctor_19_);
v___f_28_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_28_, 0, v_toFunctor_19_);
v___f_29_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_29_, 0, v_toFunctor_19_);
v___x_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_30_, 0, v___f_28_);
lean_ctor_set(v___x_30_, 1, v___f_29_);
v___f_31_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_31_, 0, v_toSeqRight_22_);
v___f_32_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_32_, 0, v_toSeqLeft_21_);
v___f_33_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_33_, 0, v_toSeq_20_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 4, v___f_31_);
lean_ctor_set(v___x_24_, 3, v___f_32_);
lean_ctor_set(v___x_24_, 2, v___f_33_);
lean_ctor_set(v___x_24_, 1, v___f_26_);
lean_ctor_set(v___x_24_, 0, v___x_30_);
v___x_35_ = v___x_24_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v___x_30_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v___f_26_);
lean_ctor_set(v_reuseFailAlloc_61_, 2, v___f_33_);
lean_ctor_set(v_reuseFailAlloc_61_, 3, v___f_32_);
lean_ctor_set(v_reuseFailAlloc_61_, 4, v___f_31_);
v___x_35_ = v_reuseFailAlloc_61_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_37_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 1, v___f_27_);
lean_ctor_set(v___x_17_, 0, v___x_35_);
v___x_37_ = v___x_17_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v___x_35_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v___f_27_);
v___x_37_ = v_reuseFailAlloc_60_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_38_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___x_39_ = l_Lean_Core_instMonadRefCoreM;
v___x_40_ = l_Lean_Core_instAddMessageContextCoreM;
lean_inc_ref(v___x_37_);
v___x_41_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_40_, v___x_37_);
v___x_42_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_42_, 0, v___x_38_);
lean_ctor_set(v___x_42_, 1, v___x_39_);
lean_ctor_set(v___x_42_, 2, v___x_41_);
v___x_43_ = l_Lean_Syntax_isLit_x3f(v_k_8_, v_x_9_);
if (lean_obj_tag(v___x_43_) == 1)
{
lean_object* v_val_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_51_; 
lean_dec_ref(v___x_42_);
lean_dec_ref(v___x_37_);
lean_dec(v_a_12_);
lean_dec_ref(v_a_11_);
lean_dec(v_x_9_);
v_val_44_ = lean_ctor_get(v___x_43_, 0);
v_isSharedCheck_51_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_51_ == 0)
{
v___x_46_ = v___x_43_;
v_isShared_47_ = v_isSharedCheck_51_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_val_44_);
lean_dec(v___x_43_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_51_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_49_; 
if (v_isShared_47_ == 0)
{
lean_ctor_set_tag(v___x_46_, 0);
v___x_49_ = v___x_46_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_val_44_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
else
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_342__overap_58_; lean_object* v___x_59_; 
lean_dec(v___x_43_);
v___x_52_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4));
v___x_53_ = lean_string_append(v___x_52_, v_name_10_);
v___x_54_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5));
v___x_55_ = lean_string_append(v___x_53_, v___x_54_);
v___x_56_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
v___x_57_ = l_Lean_MessageData_ofFormat(v___x_56_);
v___x_342__overap_58_ = l_Lean_throwErrorAt___redArg(v___x_37_, v___x_42_, v_x_9_, v___x_57_);
v___x_59_ = lean_apply_3(v___x_342__overap_58_, v_a_11_, v_a_12_, lean_box(0));
return v___x_59_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___boxed(lean_object* v_k_66_, lean_object* v_x_67_, lean_object* v_name_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit(v_k_66_, v_x_67_, v_name_68_, v_a_69_, v_a_70_);
lean_dec_ref(v_name_68_);
lean_dec(v_k_66_);
return v_res_72_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_73_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1);
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
lean_ctor_set(v___x_78_, 2, v___x_77_);
lean_ctor_set(v___x_78_, 3, v___x_76_);
lean_ctor_set(v___x_78_, 4, v___x_76_);
lean_ctor_set(v___x_78_, 5, v___x_76_);
lean_ctor_set(v___x_78_, 6, v___x_76_);
lean_ctor_set(v___x_78_, 7, v___x_76_);
lean_ctor_set(v___x_78_, 8, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_unsigned_to_nat(32u);
v___x_80_ = lean_mk_empty_array_with_capacity(v___x_79_);
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_82_ = ((size_t)5ULL);
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = lean_unsigned_to_nat(32u);
v___x_85_ = lean_mk_empty_array_with_capacity(v___x_84_);
v___x_86_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3);
v___x_87_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___x_85_);
lean_ctor_set(v___x_87_, 2, v___x_83_);
lean_ctor_set(v___x_87_, 3, v___x_83_);
lean_ctor_set_usize(v___x_87_, 4, v___x_82_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_88_ = lean_box(1);
v___x_89_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4);
v___x_90_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1);
v___x_91_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v___x_89_);
lean_ctor_set(v___x_91_, 2, v___x_88_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(lean_object* v_msgData_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v___x_96_; lean_object* v_env_97_; lean_object* v_options_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_96_ = lean_st_ref_get(v___y_94_);
v_env_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc_ref(v_env_97_);
lean_dec(v___x_96_);
v_options_98_ = lean_ctor_get(v___y_93_, 2);
v___x_99_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2);
v___x_100_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_98_);
v___x_101_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_101_, 0, v_env_97_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
lean_ctor_set(v___x_101_, 2, v___x_100_);
lean_ctor_set(v___x_101_, 3, v_options_98_);
v___x_102_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v_msgData_92_);
v___x_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(v_msgData_104_, v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(lean_object* v_msg_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_ref_113_; lean_object* v___x_114_; lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_123_; 
v_ref_113_ = lean_ctor_get(v___y_110_, 5);
v___x_114_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(v_msg_109_, v___y_110_, v___y_111_);
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_123_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_123_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_123_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; lean_object* v___x_121_; 
lean_inc(v_ref_113_);
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v_ref_113_);
lean_ctor_set(v___x_119_, 1, v_a_115_);
if (v_isShared_118_ == 0)
{
lean_ctor_set_tag(v___x_117_, 1);
lean_ctor_set(v___x_117_, 0, v___x_119_);
v___x_121_ = v___x_117_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg___boxed(lean_object* v_msg_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v_msg_124_, v___y_125_, v___y_126_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(lean_object* v_ref_129_, lean_object* v_msg_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v_fileName_134_; lean_object* v_fileMap_135_; lean_object* v_options_136_; lean_object* v_currRecDepth_137_; lean_object* v_maxRecDepth_138_; lean_object* v_ref_139_; lean_object* v_currNamespace_140_; lean_object* v_openDecls_141_; lean_object* v_initHeartbeats_142_; lean_object* v_maxHeartbeats_143_; lean_object* v_quotContext_144_; lean_object* v_currMacroScope_145_; uint8_t v_diag_146_; lean_object* v_cancelTk_x3f_147_; uint8_t v_suppressElabErrors_148_; lean_object* v_inheritedTraceOptions_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_158_; 
v_fileName_134_ = lean_ctor_get(v___y_131_, 0);
v_fileMap_135_ = lean_ctor_get(v___y_131_, 1);
v_options_136_ = lean_ctor_get(v___y_131_, 2);
v_currRecDepth_137_ = lean_ctor_get(v___y_131_, 3);
v_maxRecDepth_138_ = lean_ctor_get(v___y_131_, 4);
v_ref_139_ = lean_ctor_get(v___y_131_, 5);
v_currNamespace_140_ = lean_ctor_get(v___y_131_, 6);
v_openDecls_141_ = lean_ctor_get(v___y_131_, 7);
v_initHeartbeats_142_ = lean_ctor_get(v___y_131_, 8);
v_maxHeartbeats_143_ = lean_ctor_get(v___y_131_, 9);
v_quotContext_144_ = lean_ctor_get(v___y_131_, 10);
v_currMacroScope_145_ = lean_ctor_get(v___y_131_, 11);
v_diag_146_ = lean_ctor_get_uint8(v___y_131_, sizeof(void*)*14);
v_cancelTk_x3f_147_ = lean_ctor_get(v___y_131_, 12);
v_suppressElabErrors_148_ = lean_ctor_get_uint8(v___y_131_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_149_ = lean_ctor_get(v___y_131_, 13);
v_isSharedCheck_158_ = !lean_is_exclusive(v___y_131_);
if (v_isSharedCheck_158_ == 0)
{
v___x_151_ = v___y_131_;
v_isShared_152_ = v_isSharedCheck_158_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_inheritedTraceOptions_149_);
lean_inc(v_cancelTk_x3f_147_);
lean_inc(v_currMacroScope_145_);
lean_inc(v_quotContext_144_);
lean_inc(v_maxHeartbeats_143_);
lean_inc(v_initHeartbeats_142_);
lean_inc(v_openDecls_141_);
lean_inc(v_currNamespace_140_);
lean_inc(v_ref_139_);
lean_inc(v_maxRecDepth_138_);
lean_inc(v_currRecDepth_137_);
lean_inc(v_options_136_);
lean_inc(v_fileMap_135_);
lean_inc(v_fileName_134_);
lean_dec(v___y_131_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_158_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v_ref_153_; lean_object* v___x_155_; 
v_ref_153_ = l_Lean_replaceRef(v_ref_129_, v_ref_139_);
lean_dec(v_ref_139_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 5, v_ref_153_);
v___x_155_ = v___x_151_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_fileName_134_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_fileMap_135_);
lean_ctor_set(v_reuseFailAlloc_157_, 2, v_options_136_);
lean_ctor_set(v_reuseFailAlloc_157_, 3, v_currRecDepth_137_);
lean_ctor_set(v_reuseFailAlloc_157_, 4, v_maxRecDepth_138_);
lean_ctor_set(v_reuseFailAlloc_157_, 5, v_ref_153_);
lean_ctor_set(v_reuseFailAlloc_157_, 6, v_currNamespace_140_);
lean_ctor_set(v_reuseFailAlloc_157_, 7, v_openDecls_141_);
lean_ctor_set(v_reuseFailAlloc_157_, 8, v_initHeartbeats_142_);
lean_ctor_set(v_reuseFailAlloc_157_, 9, v_maxHeartbeats_143_);
lean_ctor_set(v_reuseFailAlloc_157_, 10, v_quotContext_144_);
lean_ctor_set(v_reuseFailAlloc_157_, 11, v_currMacroScope_145_);
lean_ctor_set(v_reuseFailAlloc_157_, 12, v_cancelTk_x3f_147_);
lean_ctor_set(v_reuseFailAlloc_157_, 13, v_inheritedTraceOptions_149_);
lean_ctor_set_uint8(v_reuseFailAlloc_157_, sizeof(void*)*14, v_diag_146_);
lean_ctor_set_uint8(v_reuseFailAlloc_157_, sizeof(void*)*14 + 1, v_suppressElabErrors_148_);
v___x_155_ = v_reuseFailAlloc_157_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v_msg_130_, v___x_155_, v___y_132_);
lean_dec_ref(v___x_155_);
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg___boxed(lean_object* v_ref_159_, lean_object* v_msg_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_ref_159_, v_msg_160_, v___y_161_, v___y_162_);
lean_dec(v___y_162_);
lean_dec(v_ref_159_);
return v_res_164_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__4));
v___x_174_ = l_Lean_stringToMessageData(v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(lean_object* v_x_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_189_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3));
lean_inc(v_x_185_);
v___x_190_ = l_Lean_Syntax_isOfKind(v_x_185_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5);
v___x_192_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_185_, v___x_191_, v_a_186_, v_a_187_);
lean_dec(v_x_185_);
return v___x_192_;
}
else
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = l_Lean_Syntax_getArg(v_x_185_, v___x_193_);
v___x_195_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7));
lean_inc(v___x_194_);
v___x_196_ = l_Lean_Syntax_isOfKind(v___x_194_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_197_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9));
v___x_198_ = l_Lean_Syntax_isOfKind(v___x_194_, v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5);
v___x_200_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_185_, v___x_199_, v_a_186_, v_a_187_);
lean_dec(v_x_185_);
return v___x_200_;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec_ref(v_a_186_);
lean_dec(v_x_185_);
v___x_201_ = lean_box(v___x_196_);
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
return v___x_202_;
}
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec(v___x_194_);
lean_dec_ref(v_a_186_);
lean_dec(v_x_185_);
v___x_203_ = lean_box(v___x_196_);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___boxed(lean_object* v_x_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(v_x_205_, v_a_206_, v_a_207_);
lean_dec(v_a_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0(lean_object* v_00_u03b1_210_, lean_object* v_ref_211_, lean_object* v_msg_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_ref_211_, v_msg_212_, v___y_213_, v___y_214_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___boxed(lean_object* v_00_u03b1_217_, lean_object* v_ref_218_, lean_object* v_msg_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0(v_00_u03b1_217_, v_ref_218_, v_msg_219_, v___y_220_, v___y_221_);
lean_dec(v___y_221_);
lean_dec(v_ref_218_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0(lean_object* v_00_u03b1_224_, lean_object* v_msg_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v_msg_225_, v___y_226_, v___y_227_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___boxed(lean_object* v_00_u03b1_230_, lean_object* v_msg_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0(v_00_u03b1_230_, v_msg_231_, v___y_232_, v___y_233_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(lean_object* v___x_236_, lean_object* v_s_237_, lean_object* v_a_238_, lean_object* v_b_239_){
_start:
{
lean_object* v_startInclusive_240_; lean_object* v_endExclusive_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v_startInclusive_240_ = lean_ctor_get(v___x_236_, 1);
v_endExclusive_241_ = lean_ctor_get(v___x_236_, 2);
v___x_242_ = lean_nat_sub(v_endExclusive_241_, v_startInclusive_240_);
v___x_243_ = lean_nat_dec_eq(v_a_238_, v___x_242_);
lean_dec(v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; uint32_t v___x_245_; uint32_t v___x_246_; uint8_t v___x_247_; 
v___x_244_ = lean_string_utf8_next_fast(v_s_237_, v_a_238_);
v___x_245_ = lean_string_utf8_get_fast(v_s_237_, v_a_238_);
lean_dec(v_a_238_);
v___x_246_ = 95;
v___x_247_ = lean_uint32_dec_eq(v___x_245_, v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; uint32_t v___x_250_; uint32_t v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_248_ = lean_unsigned_to_nat(10u);
v___x_249_ = lean_nat_mul(v_b_239_, v___x_248_);
lean_dec(v_b_239_);
v___x_250_ = 48;
v___x_251_ = lean_uint32_sub(v___x_245_, v___x_250_);
v___x_252_ = lean_uint32_to_nat(v___x_251_);
v___x_253_ = lean_nat_add(v___x_249_, v___x_252_);
lean_dec(v___x_252_);
lean_dec(v___x_249_);
v_a_238_ = v___x_244_;
v_b_239_ = v___x_253_;
goto _start;
}
else
{
v_a_238_ = v___x_244_;
goto _start;
}
}
else
{
lean_dec(v_a_238_);
return v_b_239_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg___boxed(lean_object* v___x_256_, lean_object* v_s_257_, lean_object* v_a_258_, lean_object* v_b_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(v___x_256_, v_s_257_, v_a_258_, v_b_259_);
lean_dec_ref(v_s_257_);
lean_dec_ref(v___x_256_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(lean_object* v_s_261_){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_string_utf8_byte_size(v_s_261_);
lean_inc_ref(v_s_261_);
v___x_264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_264_, 0, v_s_261_);
lean_ctor_set(v___x_264_, 1, v___x_262_);
lean_ctor_set(v___x_264_, 2, v___x_263_);
v___x_265_ = l_String_Slice_positions(v___x_264_);
v___x_266_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(v___x_264_, v_s_261_, v___x_265_, v___x_262_);
lean_dec_ref(v_s_261_);
lean_dec_ref(v___x_264_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0(lean_object* v___x_267_, lean_object* v_s_268_, lean_object* v_inst_269_, lean_object* v_R_270_, lean_object* v_a_271_, lean_object* v_b_272_, lean_object* v_c_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(v___x_267_, v_s_268_, v_a_271_, v_b_272_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___boxed(lean_object* v___x_275_, lean_object* v_s_276_, lean_object* v_inst_277_, lean_object* v_R_278_, lean_object* v_a_279_, lean_object* v_b_280_, lean_object* v_c_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0(v___x_275_, v_s_276_, v_inst_277_, v_R_278_, v_a_279_, v_b_280_, v_c_281_);
lean_dec_ref(v_s_276_);
lean_dec_ref(v___x_275_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeSign(lean_object* v_s_283_){
_start:
{
uint32_t v___y_285_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = lean_string_utf8_byte_size(v_s_283_);
lean_inc_ref(v_s_283_);
v___x_310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_310_, 0, v_s_283_);
lean_ctor_set(v___x_310_, 1, v___x_308_);
lean_ctor_set(v___x_310_, 2, v___x_309_);
v___x_311_ = l_String_Slice_Pos_get_x3f(v___x_310_, v___x_308_);
lean_dec_ref(v___x_310_);
if (lean_obj_tag(v___x_311_) == 0)
{
uint32_t v___x_312_; 
v___x_312_ = 65;
v___y_285_ = v___x_312_;
goto v___jp_284_;
}
else
{
lean_object* v_val_313_; uint32_t v___x_314_; 
v_val_313_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_val_313_);
lean_dec_ref(v___x_311_);
v___x_314_ = lean_unbox_uint32(v_val_313_);
lean_dec(v_val_313_);
v___y_285_ = v___x_314_;
goto v___jp_284_;
}
v___jp_284_:
{
uint32_t v___x_286_; uint8_t v___x_287_; 
v___x_286_ = 45;
v___x_287_ = lean_uint32_dec_eq(v___y_285_, v___x_286_);
if (v___x_287_ == 0)
{
uint32_t v___x_288_; uint8_t v___x_289_; 
v___x_288_ = 43;
v___x_289_ = lean_uint32_dec_eq(v___y_285_, v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_box(v___x_289_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v_s_283_);
return v___x_291_;
}
else
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_292_ = lean_unsigned_to_nat(1u);
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = lean_string_utf8_byte_size(v_s_283_);
lean_inc_ref(v_s_283_);
v___x_295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_295_, 0, v_s_283_);
lean_ctor_set(v___x_295_, 1, v___x_293_);
lean_ctor_set(v___x_295_, 2, v___x_294_);
v___x_296_ = l_String_Slice_Pos_nextn(v___x_295_, v___x_293_, v___x_292_);
lean_dec_ref(v___x_295_);
v___x_297_ = lean_string_utf8_extract(v_s_283_, v___x_296_, v___x_294_);
lean_dec(v___x_296_);
lean_dec_ref(v_s_283_);
v___x_298_ = lean_box(v___x_287_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___x_297_);
return v___x_299_;
}
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_300_ = lean_unsigned_to_nat(1u);
v___x_301_ = lean_unsigned_to_nat(0u);
v___x_302_ = lean_string_utf8_byte_size(v_s_283_);
lean_inc_ref(v_s_283_);
v___x_303_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_303_, 0, v_s_283_);
lean_ctor_set(v___x_303_, 1, v___x_301_);
lean_ctor_set(v___x_303_, 2, v___x_302_);
v___x_304_ = l_String_Slice_Pos_nextn(v___x_303_, v___x_301_, v___x_300_);
lean_dec_ref(v___x_303_);
v___x_305_ = lean_string_utf8_extract(v_s_283_, v___x_304_, v___x_302_);
lean_dec(v___x_304_);
lean_dec_ref(v_s_283_);
v___x_306_ = lean_box(v___x_287_);
v___x_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v___x_305_);
return v___x_307_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(lean_object* v_s_315_){
_start:
{
uint8_t v_fst_317_; lean_object* v_snd_318_; uint32_t v___y_324_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_string_utf8_byte_size(v_s_315_);
lean_inc_ref(v_s_315_);
v___x_343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_343_, 0, v_s_315_);
lean_ctor_set(v___x_343_, 1, v___x_341_);
lean_ctor_set(v___x_343_, 2, v___x_342_);
v___x_344_ = l_String_Slice_Pos_get_x3f(v___x_343_, v___x_341_);
lean_dec_ref(v___x_343_);
if (lean_obj_tag(v___x_344_) == 0)
{
uint32_t v___x_345_; 
v___x_345_ = 65;
v___y_324_ = v___x_345_;
goto v___jp_323_;
}
else
{
lean_object* v_val_346_; uint32_t v___x_347_; 
v_val_346_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_val_346_);
lean_dec_ref(v___x_344_);
v___x_347_ = lean_unbox_uint32(v_val_346_);
lean_dec(v_val_346_);
v___y_324_ = v___x_347_;
goto v___jp_323_;
}
v___jp_316_:
{
if (v_fst_317_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(v_snd_318_);
v___x_320_ = lean_nat_to_int(v___x_319_);
return v___x_320_;
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(v_snd_318_);
v___x_322_ = l_Int_negOfNat(v___x_321_);
lean_dec(v___x_321_);
return v___x_322_;
}
}
v___jp_323_:
{
uint32_t v___x_325_; uint8_t v___x_326_; 
v___x_325_ = 45;
v___x_326_ = lean_uint32_dec_eq(v___y_324_, v___x_325_);
if (v___x_326_ == 0)
{
uint32_t v___x_327_; uint8_t v___x_328_; 
v___x_327_ = 43;
v___x_328_ = lean_uint32_dec_eq(v___y_324_, v___x_327_);
if (v___x_328_ == 0)
{
v_fst_317_ = v___x_328_;
v_snd_318_ = v_s_315_;
goto v___jp_316_;
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_329_ = lean_unsigned_to_nat(1u);
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = lean_string_utf8_byte_size(v_s_315_);
lean_inc_ref(v_s_315_);
v___x_332_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_332_, 0, v_s_315_);
lean_ctor_set(v___x_332_, 1, v___x_330_);
lean_ctor_set(v___x_332_, 2, v___x_331_);
v___x_333_ = l_String_Slice_Pos_nextn(v___x_332_, v___x_330_, v___x_329_);
lean_dec_ref(v___x_332_);
v___x_334_ = lean_string_utf8_extract(v_s_315_, v___x_333_, v___x_331_);
lean_dec(v___x_333_);
lean_dec_ref(v_s_315_);
v_fst_317_ = v___x_326_;
v_snd_318_ = v___x_334_;
goto v___jp_316_;
}
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_335_ = lean_unsigned_to_nat(1u);
v___x_336_ = lean_unsigned_to_nat(0u);
v___x_337_ = lean_string_utf8_byte_size(v_s_315_);
lean_inc_ref(v_s_315_);
v___x_338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_338_, 0, v_s_315_);
lean_ctor_set(v___x_338_, 1, v___x_336_);
lean_ctor_set(v___x_338_, 2, v___x_337_);
v___x_339_ = l_String_Slice_Pos_nextn(v___x_338_, v___x_336_, v___x_335_);
lean_dec_ref(v___x_338_);
v___x_340_ = lean_string_utf8_extract(v_s_315_, v___x_339_, v___x_337_);
lean_dec(v___x_339_);
lean_dec_ref(v_s_315_);
v_fst_317_ = v___x_326_;
v_snd_318_ = v___x_340_;
goto v___jp_316_;
}
}
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__3));
v___x_357_ = l_Lean_MessageData_ofFormat(v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(lean_object* v_x_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_a_363_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1));
v___x_367_ = l_Lean_Syntax_isLit_x3f(v___x_366_, v_x_358_);
if (lean_obj_tag(v___x_367_) == 1)
{
lean_object* v_val_368_; 
lean_dec_ref(v_a_359_);
v_val_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_val_368_);
lean_dec_ref(v___x_367_);
v_a_363_ = v_val_368_;
goto v___jp_362_;
}
else
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec(v___x_367_);
v___x_369_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4);
v___x_370_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_358_, v___x_369_, v_a_359_, v_a_360_);
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
v___jp_362_:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(v_a_363_);
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___boxed(lean_object* v_x_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(v_x_379_, v_a_380_, v_a_381_);
lean_dec(v_a_381_);
lean_dec(v_x_379_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(lean_object* v___x_384_, lean_object* v_s_385_, lean_object* v_a_386_, lean_object* v_b_387_){
_start:
{
lean_object* v_startInclusive_388_; lean_object* v_endExclusive_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v_startInclusive_388_ = lean_ctor_get(v___x_384_, 1);
v_endExclusive_389_ = lean_ctor_get(v___x_384_, 2);
v___x_390_ = lean_nat_sub(v_endExclusive_389_, v_startInclusive_388_);
v___x_391_ = lean_nat_dec_eq(v_a_386_, v___x_390_);
lean_dec(v___x_390_);
if (v___x_391_ == 0)
{
lean_object* v_fst_392_; lean_object* v_snd_393_; lean_object* v___x_394_; uint32_t v___x_395_; uint32_t v___x_396_; uint8_t v___x_397_; 
v_fst_392_ = lean_ctor_get(v_b_387_, 0);
v_snd_393_ = lean_ctor_get(v_b_387_, 1);
v___x_394_ = lean_string_utf8_next_fast(v_s_385_, v_a_386_);
v___x_395_ = lean_string_utf8_get_fast(v_s_385_, v_a_386_);
lean_dec(v_a_386_);
v___x_396_ = 95;
v___x_397_ = lean_uint32_dec_eq(v___x_395_, v___x_396_);
if (v___x_397_ == 0)
{
lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_420_; 
lean_inc(v_snd_393_);
lean_inc(v_fst_392_);
v_isSharedCheck_420_ = !lean_is_exclusive(v_b_387_);
if (v_isSharedCheck_420_ == 0)
{
lean_object* v_unused_421_; lean_object* v_unused_422_; 
v_unused_421_ = lean_ctor_get(v_b_387_, 1);
lean_dec(v_unused_421_);
v_unused_422_ = lean_ctor_get(v_b_387_, 0);
lean_dec(v_unused_422_);
v___x_399_ = v_b_387_;
v_isShared_400_ = v_isSharedCheck_420_;
goto v_resetjp_398_;
}
else
{
lean_dec(v_b_387_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_420_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
uint32_t v___x_401_; uint8_t v___x_402_; 
v___x_401_ = 46;
v___x_402_ = lean_uint32_dec_eq(v___x_395_, v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; uint32_t v___x_405_; uint32_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_412_; 
v___x_403_ = lean_unsigned_to_nat(10u);
v___x_404_ = lean_nat_mul(v_fst_392_, v___x_403_);
lean_dec(v_fst_392_);
v___x_405_ = 48;
v___x_406_ = lean_uint32_sub(v___x_395_, v___x_405_);
v___x_407_ = lean_uint32_to_nat(v___x_406_);
v___x_408_ = lean_nat_add(v___x_404_, v___x_407_);
lean_dec(v___x_407_);
lean_dec(v___x_404_);
v___x_409_ = lean_unsigned_to_nat(1u);
v___x_410_ = lean_nat_add(v_snd_393_, v___x_409_);
lean_dec(v_snd_393_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 1, v___x_410_);
lean_ctor_set(v___x_399_, 0, v___x_408_);
v___x_412_ = v___x_399_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_408_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v___x_410_);
v___x_412_ = v_reuseFailAlloc_414_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
v_a_386_ = v___x_394_;
v_b_387_ = v___x_412_;
goto _start;
}
}
else
{
lean_object* v___x_415_; lean_object* v___x_417_; 
lean_dec(v_snd_393_);
v___x_415_ = lean_unsigned_to_nat(0u);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 1, v___x_415_);
v___x_417_ = v___x_399_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_fst_392_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v___x_415_);
v___x_417_ = v_reuseFailAlloc_419_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
v_a_386_ = v___x_394_;
v_b_387_ = v___x_417_;
goto _start;
}
}
}
}
else
{
v_a_386_ = v___x_394_;
goto _start;
}
}
else
{
lean_dec(v_a_386_);
return v_b_387_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg___boxed(lean_object* v___x_424_, lean_object* v_s_425_, lean_object* v_a_426_, lean_object* v_b_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(v___x_424_, v_s_425_, v_a_426_, v_b_427_);
lean_dec_ref(v_s_425_);
lean_dec_ref(v___x_424_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(lean_object* v_s_429_){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v_fst_437_; lean_object* v_snd_438_; uint8_t v___x_439_; 
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_431_ = lean_string_length(v_s_429_);
v___x_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = lean_string_utf8_byte_size(v_s_429_);
lean_inc_ref(v_s_429_);
v___x_434_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_434_, 0, v_s_429_);
lean_ctor_set(v___x_434_, 1, v___x_430_);
lean_ctor_set(v___x_434_, 2, v___x_433_);
v___x_435_ = l_String_Slice_positions(v___x_434_);
v___x_436_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(v___x_434_, v_s_429_, v___x_435_, v___x_432_);
lean_dec_ref(v_s_429_);
lean_dec_ref(v___x_434_);
v_fst_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_fst_437_);
v_snd_438_ = lean_ctor_get(v___x_436_, 1);
lean_inc(v_snd_438_);
v___x_439_ = lean_nat_dec_le(v___x_431_, v_snd_438_);
lean_dec(v_snd_438_);
if (v___x_439_ == 0)
{
lean_dec(v_fst_437_);
return v___x_436_;
}
else
{
lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; lean_object* v_unused_448_; 
v_unused_447_ = lean_ctor_get(v___x_436_, 1);
lean_dec(v_unused_447_);
v_unused_448_ = lean_ctor_get(v___x_436_, 0);
lean_dec(v_unused_448_);
v___x_441_ = v___x_436_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_dec(v___x_436_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 1, v___x_430_);
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_fst_437_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v___x_430_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0(lean_object* v___x_449_, lean_object* v_s_450_, lean_object* v_inst_451_, lean_object* v_R_452_, lean_object* v_a_453_, lean_object* v_b_454_, lean_object* v_c_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(v___x_449_, v_s_450_, v_a_453_, v_b_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___boxed(lean_object* v___x_457_, lean_object* v_s_458_, lean_object* v_inst_459_, lean_object* v_R_460_, lean_object* v_a_461_, lean_object* v_b_462_, lean_object* v_c_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0(v___x_457_, v_s_458_, v_inst_459_, v_R_460_, v_a_461_, v_b_462_, v_c_463_);
lean_dec_ref(v_s_458_);
lean_dec_ref(v___x_457_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(lean_object* v_s_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0));
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___boxed(lean_object* v_s_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(v_s_469_);
lean_dec_ref(v_s_469_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(lean_object* v_s_471_, lean_object* v___x_472_, lean_object* v___x_473_, lean_object* v_a_474_, lean_object* v_b_475_){
_start:
{
lean_object* v_it_477_; lean_object* v_startInclusive_478_; lean_object* v_endExclusive_479_; 
if (lean_obj_tag(v_a_474_) == 0)
{
lean_object* v_currPos_484_; lean_object* v_searcher_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_515_; 
v_currPos_484_ = lean_ctor_get(v_a_474_, 0);
v_searcher_485_ = lean_ctor_get(v_a_474_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v_a_474_);
if (v_isSharedCheck_515_ == 0)
{
v___x_487_ = v_a_474_;
v_isShared_488_ = v_isSharedCheck_515_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_searcher_485_);
lean_inc(v_currPos_484_);
lean_dec(v_a_474_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_515_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
uint8_t v___y_490_; lean_object* v_startInclusive_505_; lean_object* v_endExclusive_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_startInclusive_505_ = lean_ctor_get(v___x_472_, 1);
v_endExclusive_506_ = lean_ctor_get(v___x_472_, 2);
v___x_507_ = lean_nat_sub(v_endExclusive_506_, v_startInclusive_505_);
v___x_508_ = lean_nat_dec_eq(v_searcher_485_, v___x_507_);
lean_dec(v___x_507_);
if (v___x_508_ == 0)
{
uint32_t v___x_509_; uint32_t v___x_510_; uint8_t v___x_511_; 
v___x_509_ = lean_string_utf8_get_fast(v_s_471_, v_searcher_485_);
v___x_510_ = 69;
v___x_511_ = lean_uint32_dec_eq(v___x_509_, v___x_510_);
if (v___x_511_ == 0)
{
uint32_t v___x_512_; uint8_t v___x_513_; 
v___x_512_ = 101;
v___x_513_ = lean_uint32_dec_eq(v___x_509_, v___x_512_);
v___y_490_ = v___x_513_;
goto v___jp_489_;
}
else
{
v___y_490_ = v___x_511_;
goto v___jp_489_;
}
}
else
{
lean_object* v___x_514_; 
lean_del_object(v___x_487_);
lean_dec(v_searcher_485_);
v___x_514_ = lean_box(1);
lean_inc(v___x_473_);
v_it_477_ = v___x_514_;
v_startInclusive_478_ = v_currPos_484_;
v_endExclusive_479_ = v___x_473_;
goto v___jp_476_;
}
v___jp_489_:
{
if (v___y_490_ == 0)
{
lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_491_ = lean_string_utf8_next_fast(v_s_471_, v_searcher_485_);
lean_dec(v_searcher_485_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 1, v___x_491_);
v___x_493_ = v___x_487_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_currPos_484_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v___x_491_);
v___x_493_ = v_reuseFailAlloc_495_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
v_a_474_ = v___x_493_;
goto _start;
}
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v_slice_499_; lean_object* v_nextIt_501_; 
v___x_496_ = lean_string_utf8_next_fast(v_s_471_, v_searcher_485_);
v___x_497_ = lean_nat_sub(v___x_496_, v_searcher_485_);
v___x_498_ = lean_nat_add(v_searcher_485_, v___x_497_);
lean_dec(v___x_497_);
v_slice_499_ = l_String_Slice_subslice_x21(v___x_472_, v_currPos_484_, v_searcher_485_);
lean_inc(v___x_498_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 1, v___x_498_);
lean_ctor_set(v___x_487_, 0, v___x_498_);
v_nextIt_501_ = v___x_487_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_498_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_498_);
v_nextIt_501_ = v_reuseFailAlloc_504_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
lean_object* v_startInclusive_502_; lean_object* v_endExclusive_503_; 
v_startInclusive_502_ = lean_ctor_get(v_slice_499_, 0);
lean_inc(v_startInclusive_502_);
v_endExclusive_503_ = lean_ctor_get(v_slice_499_, 1);
lean_inc(v_endExclusive_503_);
lean_dec_ref(v_slice_499_);
v_it_477_ = v_nextIt_501_;
v_startInclusive_478_ = v_startInclusive_502_;
v_endExclusive_479_ = v_endExclusive_503_;
goto v___jp_476_;
}
}
}
}
}
else
{
lean_dec(v___x_473_);
lean_dec_ref(v_s_471_);
return v_b_475_;
}
v___jp_476_:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
lean_inc_ref(v_s_471_);
v___x_480_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_480_, 0, v_s_471_);
lean_ctor_set(v___x_480_, 1, v_startInclusive_478_);
lean_ctor_set(v___x_480_, 2, v_endExclusive_479_);
v___x_481_ = l_String_Slice_toString(v___x_480_);
lean_dec_ref(v___x_480_);
v___x_482_ = lean_array_push(v_b_475_, v___x_481_);
v_a_474_ = v_it_477_;
v_b_475_ = v___x_482_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg___boxed(lean_object* v_s_516_, lean_object* v___x_517_, lean_object* v___x_518_, lean_object* v_a_519_, lean_object* v_b_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_516_, v___x_517_, v___x_518_, v_a_519_, v_b_520_);
lean_dec_ref(v___x_517_);
return v_res_521_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = lean_nat_to_int(v___x_522_);
return v___x_523_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_524_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0);
v___x_525_ = lean_unsigned_to_nat(0u);
v___x_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
lean_ctor_set(v___x_526_, 1, v___x_524_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp(lean_object* v_s_529_){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = lean_string_utf8_byte_size(v_s_529_);
lean_inc_ref(v_s_529_);
v___x_534_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_534_, 0, v_s_529_);
lean_ctor_set(v___x_534_, 1, v___x_532_);
lean_ctor_set(v___x_534_, 2, v___x_533_);
v___x_535_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(v___x_534_);
v___x_536_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2));
v___x_537_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_529_, v___x_534_, v___x_533_, v___x_535_, v___x_536_);
lean_dec_ref(v___x_534_);
v___x_538_ = lean_array_to_list(v___x_537_);
if (lean_obj_tag(v___x_538_) == 1)
{
lean_object* v_tail_539_; 
v_tail_539_ = lean_ctor_get(v___x_538_, 1);
lean_inc(v_tail_539_);
if (lean_obj_tag(v_tail_539_) == 0)
{
lean_object* v_head_540_; lean_object* v___x_541_; lean_object* v_fst_542_; lean_object* v_snd_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_551_; 
v_head_540_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_head_540_);
lean_dec_ref(v___x_538_);
v___x_541_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(v_head_540_);
v_fst_542_ = lean_ctor_get(v___x_541_, 0);
v_snd_543_ = lean_ctor_get(v___x_541_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_551_ == 0)
{
v___x_545_ = v___x_541_;
v_isShared_546_ = v_isSharedCheck_551_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_snd_543_);
lean_inc(v_fst_542_);
lean_dec(v___x_541_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_551_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = l_Int_negOfNat(v_snd_543_);
lean_dec(v_snd_543_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 1, v___x_547_);
v___x_549_ = v___x_545_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_fst_542_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
else
{
lean_object* v_tail_552_; 
v_tail_552_ = lean_ctor_get(v_tail_539_, 1);
if (lean_obj_tag(v_tail_552_) == 0)
{
lean_object* v_head_553_; lean_object* v_head_554_; lean_object* v___x_555_; lean_object* v_fst_556_; lean_object* v_snd_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_567_; 
v_head_553_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_head_553_);
lean_dec_ref(v___x_538_);
v_head_554_ = lean_ctor_get(v_tail_539_, 0);
lean_inc(v_head_554_);
lean_dec_ref(v_tail_539_);
v___x_555_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(v_head_553_);
v_fst_556_ = lean_ctor_get(v___x_555_, 0);
v_snd_557_ = lean_ctor_get(v___x_555_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_567_ == 0)
{
v___x_559_ = v___x_555_;
v_isShared_560_ = v_isSharedCheck_567_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_snd_557_);
lean_inc(v_fst_556_);
lean_dec(v___x_555_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_567_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v_exp_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_565_; 
v_exp_561_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(v_head_554_);
v___x_562_ = l_Int_negOfNat(v_snd_557_);
lean_dec(v_snd_557_);
v___x_563_ = lean_int_add(v___x_562_, v_exp_561_);
lean_dec(v_exp_561_);
lean_dec(v___x_562_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 1, v___x_563_);
v___x_565_ = v___x_559_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_fst_556_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
else
{
lean_dec_ref(v_tail_539_);
lean_dec_ref(v___x_538_);
goto v___jp_530_;
}
}
}
else
{
lean_dec(v___x_538_);
goto v___jp_530_;
}
v___jp_530_:
{
lean_object* v___x_531_; 
v___x_531_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1);
return v___x_531_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1(lean_object* v_s_568_, lean_object* v___x_569_, lean_object* v___x_570_, lean_object* v_inst_571_, lean_object* v_R_572_, lean_object* v_a_573_, lean_object* v_b_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_568_, v___x_569_, v___x_570_, v_a_573_, v_b_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___boxed(lean_object* v_s_576_, lean_object* v___x_577_, lean_object* v___x_578_, lean_object* v_inst_579_, lean_object* v_R_580_, lean_object* v_a_581_, lean_object* v_b_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1(v_s_576_, v___x_577_, v___x_578_, v_inst_579_, v_R_580_, v_a_581_, v_b_582_);
lean_dec_ref(v___x_577_);
return v_res_583_;
}
}
static double _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2(void){
_start:
{
lean_object* v___x_586_; double v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_float_of_nat(v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT double l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(lean_object* v_s_588_){
_start:
{
lean_object* v___x_589_; lean_object* v_fst_590_; lean_object* v_snd_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_589_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeSign(v_s_588_);
v_fst_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_fst_590_);
v_snd_591_ = lean_ctor_get(v___x_589_, 1);
lean_inc(v_snd_591_);
lean_dec_ref(v___x_589_);
v___x_592_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0));
v___x_593_ = lean_string_dec_eq(v_snd_591_, v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1));
v___x_595_ = lean_string_dec_eq(v_snd_591_, v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v_fst_597_; lean_object* v_snd_598_; lean_object* v___x_599_; uint8_t v___x_600_; lean_object* v___x_601_; double v_flt_602_; uint8_t v___x_603_; 
v___x_596_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp(v_snd_591_);
v_fst_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_fst_597_);
v_snd_598_ = lean_ctor_get(v___x_596_, 1);
lean_inc(v_snd_598_);
lean_dec_ref(v___x_596_);
v___x_599_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0);
v___x_600_ = lean_int_dec_lt(v_snd_598_, v___x_599_);
v___x_601_ = lean_nat_abs(v_snd_598_);
lean_dec(v_snd_598_);
v_flt_602_ = l_Float_ofScientific(v_fst_597_, v___x_600_, v___x_601_);
lean_dec(v_fst_597_);
v___x_603_ = lean_unbox(v_fst_590_);
lean_dec(v_fst_590_);
if (v___x_603_ == 0)
{
return v_flt_602_;
}
else
{
double v___x_604_; 
v___x_604_ = lean_float_negate(v_flt_602_);
return v___x_604_;
}
}
else
{
uint8_t v___x_605_; 
lean_dec(v_snd_591_);
v___x_605_ = lean_unbox(v_fst_590_);
lean_dec(v_fst_590_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; double v___x_608_; double v___x_609_; double v___x_610_; 
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = lean_unsigned_to_nat(1u);
v___x_608_ = l_Float_ofScientific(v___x_606_, v___x_595_, v___x_607_);
v___x_609_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_610_ = lean_float_div(v___x_608_, v___x_609_);
return v___x_610_;
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; double v___x_613_; double v___x_614_; double v___x_615_; double v___x_616_; 
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = lean_unsigned_to_nat(1u);
v___x_613_ = l_Float_ofScientific(v___x_611_, v___x_595_, v___x_612_);
v___x_614_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_615_ = lean_float_div(v___x_613_, v___x_614_);
v___x_616_ = lean_float_negate(v___x_615_);
return v___x_616_;
}
}
}
else
{
uint8_t v___x_617_; 
lean_dec(v_snd_591_);
v___x_617_ = lean_unbox(v_fst_590_);
lean_dec(v_fst_590_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; double v___x_620_; double v___x_621_; double v___x_622_; 
v___x_618_ = lean_unsigned_to_nat(10u);
v___x_619_ = lean_unsigned_to_nat(1u);
v___x_620_ = l_Float_ofScientific(v___x_618_, v___x_593_, v___x_619_);
v___x_621_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_622_ = lean_float_div(v___x_620_, v___x_621_);
return v___x_622_;
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; double v___x_625_; double v___x_626_; double v___x_627_; double v___x_628_; 
v___x_623_ = lean_unsigned_to_nat(10u);
v___x_624_ = lean_unsigned_to_nat(1u);
v___x_625_ = l_Float_ofScientific(v___x_623_, v___x_593_, v___x_624_);
v___x_626_ = lean_float_negate(v___x_625_);
v___x_627_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_628_ = lean_float_div(v___x_626_, v___x_627_);
return v___x_628_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___boxed(lean_object* v_s_629_){
_start:
{
double v_res_630_; lean_object* v_r_631_; 
v_res_630_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(v_s_629_);
v_r_631_ = lean_box_float(v_res_630_);
return v_r_631_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__3));
v___x_641_ = l_Lean_MessageData_ofFormat(v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(lean_object* v_x_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_a_647_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1));
v___x_652_ = l_Lean_Syntax_isLit_x3f(v___x_651_, v_x_642_);
if (lean_obj_tag(v___x_652_) == 1)
{
lean_object* v_val_653_; 
lean_dec_ref(v_a_643_);
v_val_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_val_653_);
lean_dec_ref(v___x_652_);
v_a_647_ = v_val_653_;
goto v___jp_646_;
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
lean_dec(v___x_652_);
v___x_654_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4);
v___x_655_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_642_, v___x_654_, v_a_643_, v_a_644_);
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
v___jp_646_:
{
double v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(v_a_647_);
v___x_649_ = lean_box_float(v___x_648_);
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___boxed(lean_object* v_x_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(v_x_664_, v_a_665_, v_a_666_);
lean_dec(v_a_666_);
lean_dec(v_x_664_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(lean_object* v___x_669_, lean_object* v___x_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_b_673_){
_start:
{
lean_object* v_startInclusive_674_; lean_object* v_endExclusive_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v_startInclusive_674_ = lean_ctor_get(v___x_669_, 1);
v_endExclusive_675_ = lean_ctor_get(v___x_669_, 2);
v___x_676_ = lean_nat_sub(v_endExclusive_675_, v_startInclusive_674_);
v___x_677_ = lean_nat_dec_eq(v_a_672_, v___x_676_);
lean_dec(v___x_676_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; uint32_t v___x_681_; uint32_t v___x_682_; uint8_t v___x_683_; 
v___x_678_ = lean_nat_add(v___x_670_, v_a_672_);
lean_dec(v_a_672_);
v___x_679_ = lean_string_utf8_next_fast(v_a_671_, v___x_678_);
v___x_680_ = lean_nat_sub(v___x_679_, v___x_670_);
v___x_681_ = lean_string_utf8_get_fast(v_a_671_, v___x_678_);
lean_dec(v___x_678_);
v___x_682_ = 95;
v___x_683_ = lean_uint32_dec_eq(v___x_681_, v___x_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; uint32_t v___x_686_; uint32_t v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_684_ = lean_unsigned_to_nat(2u);
v___x_685_ = lean_nat_mul(v_b_673_, v___x_684_);
lean_dec(v_b_673_);
v___x_686_ = 48;
v___x_687_ = lean_uint32_sub(v___x_681_, v___x_686_);
v___x_688_ = lean_uint32_to_nat(v___x_687_);
v___x_689_ = lean_nat_add(v___x_685_, v___x_688_);
lean_dec(v___x_688_);
lean_dec(v___x_685_);
v_a_672_ = v___x_680_;
v_b_673_ = v___x_689_;
goto _start;
}
else
{
v_a_672_ = v___x_680_;
goto _start;
}
}
else
{
lean_dec(v_a_672_);
return v_b_673_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg___boxed(lean_object* v___x_692_, lean_object* v___x_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_b_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_692_, v___x_693_, v_a_694_, v_a_695_, v_b_696_);
lean_dec_ref(v_a_694_);
lean_dec(v___x_693_);
lean_dec_ref(v___x_692_);
return v_res_697_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__3));
v___x_707_ = l_Lean_MessageData_ofFormat(v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(lean_object* v_x_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_a_713_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1));
v___x_724_ = l_Lean_Syntax_isLit_x3f(v___x_723_, v_x_708_);
if (lean_obj_tag(v___x_724_) == 1)
{
lean_object* v_val_725_; 
lean_dec_ref(v_a_709_);
v_val_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_val_725_);
lean_dec_ref(v___x_724_);
v_a_713_ = v_val_725_;
goto v___jp_712_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec(v___x_724_);
v___x_726_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4);
v___x_727_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_708_, v___x_726_, v_a_709_, v_a_710_);
v_a_728_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_727_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
v___jp_712_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_714_ = lean_unsigned_to_nat(0u);
v___x_715_ = lean_unsigned_to_nat(2u);
v___x_716_ = lean_string_utf8_byte_size(v_a_713_);
lean_inc_ref(v_a_713_);
v___x_717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_717_, 0, v_a_713_);
lean_ctor_set(v___x_717_, 1, v___x_714_);
lean_ctor_set(v___x_717_, 2, v___x_716_);
v___x_718_ = l_String_Slice_Pos_nextn(v___x_717_, v___x_714_, v___x_715_);
lean_dec_ref(v___x_717_);
lean_inc(v___x_718_);
lean_inc_ref(v_a_713_);
v___x_719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_719_, 0, v_a_713_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
lean_ctor_set(v___x_719_, 2, v___x_716_);
v___x_720_ = l_String_Slice_positions(v___x_719_);
v___x_721_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_719_, v___x_718_, v_a_713_, v___x_720_, v___x_714_);
lean_dec_ref(v_a_713_);
lean_dec(v___x_718_);
lean_dec_ref(v___x_719_);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___boxed(lean_object* v_x_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(v_x_736_, v_a_737_, v_a_738_);
lean_dec(v_a_738_);
lean_dec(v_x_736_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0(lean_object* v___x_741_, lean_object* v___x_742_, lean_object* v_a_743_, lean_object* v_inst_744_, lean_object* v_R_745_, lean_object* v_a_746_, lean_object* v_b_747_, lean_object* v_c_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_741_, v___x_742_, v_a_743_, v_a_746_, v_b_747_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___boxed(lean_object* v___x_750_, lean_object* v___x_751_, lean_object* v_a_752_, lean_object* v_inst_753_, lean_object* v_R_754_, lean_object* v_a_755_, lean_object* v_b_756_, lean_object* v_c_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0(v___x_750_, v___x_751_, v_a_752_, v_inst_753_, v_R_754_, v_a_755_, v_b_756_, v_c_757_);
lean_dec_ref(v_a_752_);
lean_dec(v___x_751_);
lean_dec_ref(v___x_750_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(lean_object* v___x_759_, lean_object* v___x_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_b_763_){
_start:
{
lean_object* v_startInclusive_764_; lean_object* v_endExclusive_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v_startInclusive_764_ = lean_ctor_get(v___x_759_, 1);
v_endExclusive_765_ = lean_ctor_get(v___x_759_, 2);
v___x_766_ = lean_nat_sub(v_endExclusive_765_, v_startInclusive_764_);
v___x_767_ = lean_nat_dec_eq(v_a_762_, v___x_766_);
lean_dec(v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; uint32_t v___x_771_; uint32_t v___x_772_; uint8_t v___x_773_; 
v___x_768_ = lean_nat_add(v___x_760_, v_a_762_);
lean_dec(v_a_762_);
v___x_769_ = lean_string_utf8_next_fast(v_a_761_, v___x_768_);
v___x_770_ = lean_nat_sub(v___x_769_, v___x_760_);
v___x_771_ = lean_string_utf8_get_fast(v_a_761_, v___x_768_);
lean_dec(v___x_768_);
v___x_772_ = 95;
v___x_773_ = lean_uint32_dec_eq(v___x_771_, v___x_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; uint32_t v___x_776_; uint32_t v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_774_ = lean_unsigned_to_nat(8u);
v___x_775_ = lean_nat_mul(v_b_763_, v___x_774_);
lean_dec(v_b_763_);
v___x_776_ = 48;
v___x_777_ = lean_uint32_sub(v___x_771_, v___x_776_);
v___x_778_ = lean_uint32_to_nat(v___x_777_);
v___x_779_ = lean_nat_add(v___x_775_, v___x_778_);
lean_dec(v___x_778_);
lean_dec(v___x_775_);
v_a_762_ = v___x_770_;
v_b_763_ = v___x_779_;
goto _start;
}
else
{
v_a_762_ = v___x_770_;
goto _start;
}
}
else
{
lean_dec(v_a_762_);
return v_b_763_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg___boxed(lean_object* v___x_782_, lean_object* v___x_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_b_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_782_, v___x_783_, v_a_784_, v_a_785_, v_b_786_);
lean_dec_ref(v_a_784_);
lean_dec(v___x_783_);
lean_dec_ref(v___x_782_);
return v_res_787_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__3));
v___x_797_ = l_Lean_MessageData_ofFormat(v___x_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(lean_object* v_x_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_a_803_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1));
v___x_814_ = l_Lean_Syntax_isLit_x3f(v___x_813_, v_x_798_);
if (lean_obj_tag(v___x_814_) == 1)
{
lean_object* v_val_815_; 
lean_dec_ref(v_a_799_);
v_val_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_val_815_);
lean_dec_ref(v___x_814_);
v_a_803_ = v_val_815_;
goto v___jp_802_;
}
else
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_dec(v___x_814_);
v___x_816_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4);
v___x_817_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_798_, v___x_816_, v_a_799_, v_a_800_);
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
v___jp_802_:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = lean_unsigned_to_nat(2u);
v___x_806_ = lean_string_utf8_byte_size(v_a_803_);
lean_inc_ref(v_a_803_);
v___x_807_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_807_, 0, v_a_803_);
lean_ctor_set(v___x_807_, 1, v___x_804_);
lean_ctor_set(v___x_807_, 2, v___x_806_);
v___x_808_ = l_String_Slice_Pos_nextn(v___x_807_, v___x_804_, v___x_805_);
lean_dec_ref(v___x_807_);
lean_inc(v___x_808_);
lean_inc_ref(v_a_803_);
v___x_809_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_809_, 0, v_a_803_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
lean_ctor_set(v___x_809_, 2, v___x_806_);
v___x_810_ = l_String_Slice_positions(v___x_809_);
v___x_811_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_809_, v___x_808_, v_a_803_, v___x_810_, v___x_804_);
lean_dec_ref(v_a_803_);
lean_dec(v___x_808_);
lean_dec_ref(v___x_809_);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___boxed(lean_object* v_x_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(v_x_826_, v_a_827_, v_a_828_);
lean_dec(v_a_828_);
lean_dec(v_x_826_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(lean_object* v___x_831_, lean_object* v___x_832_, lean_object* v_a_833_, lean_object* v_inst_834_, lean_object* v_R_835_, lean_object* v_a_836_, lean_object* v_b_837_, lean_object* v_c_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_831_, v___x_832_, v_a_833_, v_a_836_, v_b_837_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___boxed(lean_object* v___x_840_, lean_object* v___x_841_, lean_object* v_a_842_, lean_object* v_inst_843_, lean_object* v_R_844_, lean_object* v_a_845_, lean_object* v_b_846_, lean_object* v_c_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(v___x_840_, v___x_841_, v_a_842_, v_inst_843_, v_R_844_, v_a_845_, v_b_846_, v_c_847_);
lean_dec_ref(v_a_842_);
lean_dec(v___x_841_);
lean_dec_ref(v___x_840_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(uint32_t v_c_849_){
_start:
{
uint32_t v___x_850_; uint8_t v___x_851_; 
v___x_850_ = 57;
v___x_851_ = lean_uint32_dec_le(v_c_849_, v___x_850_);
if (v___x_851_ == 0)
{
uint32_t v___x_852_; uint8_t v___x_853_; 
v___x_852_ = 70;
v___x_853_ = lean_uint32_dec_le(v_c_849_, v___x_852_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; uint32_t v___x_855_; uint32_t v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_854_ = lean_unsigned_to_nat(10u);
v___x_855_ = 97;
v___x_856_ = lean_uint32_sub(v_c_849_, v___x_855_);
v___x_857_ = lean_uint32_to_nat(v___x_856_);
v___x_858_ = lean_nat_add(v___x_854_, v___x_857_);
lean_dec(v___x_857_);
return v___x_858_;
}
else
{
lean_object* v___x_859_; uint32_t v___x_860_; uint32_t v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_859_ = lean_unsigned_to_nat(10u);
v___x_860_ = 65;
v___x_861_ = lean_uint32_sub(v_c_849_, v___x_860_);
v___x_862_ = lean_uint32_to_nat(v___x_861_);
v___x_863_ = lean_nat_add(v___x_859_, v___x_862_);
lean_dec(v___x_862_);
return v___x_863_;
}
}
else
{
uint32_t v___x_864_; uint32_t v___x_865_; lean_object* v___x_866_; 
v___x_864_ = 48;
v___x_865_ = lean_uint32_sub(v_c_849_, v___x_864_);
v___x_866_ = lean_uint32_to_nat(v___x_865_);
return v___x_866_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit___boxed(lean_object* v_c_867_){
_start:
{
uint32_t v_c_boxed_868_; lean_object* v_res_869_; 
v_c_boxed_868_ = lean_unbox_uint32(v_c_867_);
lean_dec(v_c_867_);
v_res_869_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v_c_boxed_868_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(lean_object* v___x_870_, lean_object* v___x_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_b_874_){
_start:
{
lean_object* v_startInclusive_875_; lean_object* v_endExclusive_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v_startInclusive_875_ = lean_ctor_get(v___x_870_, 1);
v_endExclusive_876_ = lean_ctor_get(v___x_870_, 2);
v___x_877_ = lean_nat_sub(v_endExclusive_876_, v_startInclusive_875_);
v___x_878_ = lean_nat_dec_eq(v_a_873_, v___x_877_);
lean_dec(v___x_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; uint32_t v___x_882_; uint32_t v___x_883_; uint8_t v___x_884_; 
v___x_879_ = lean_nat_add(v___x_871_, v_a_873_);
lean_dec(v_a_873_);
v___x_880_ = lean_string_utf8_next_fast(v_a_872_, v___x_879_);
v___x_881_ = lean_nat_sub(v___x_880_, v___x_871_);
v___x_882_ = lean_string_utf8_get_fast(v_a_872_, v___x_879_);
lean_dec(v___x_879_);
v___x_883_ = 95;
v___x_884_ = lean_uint32_dec_eq(v___x_882_, v___x_883_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_885_ = lean_unsigned_to_nat(16u);
v___x_886_ = lean_nat_mul(v_b_874_, v___x_885_);
lean_dec(v_b_874_);
v___x_887_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v___x_882_);
v___x_888_ = lean_nat_add(v___x_886_, v___x_887_);
lean_dec(v___x_887_);
lean_dec(v___x_886_);
v_a_873_ = v___x_881_;
v_b_874_ = v___x_888_;
goto _start;
}
else
{
v_a_873_ = v___x_881_;
goto _start;
}
}
else
{
lean_dec(v_a_873_);
return v_b_874_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg___boxed(lean_object* v___x_891_, lean_object* v___x_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_b_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_891_, v___x_892_, v_a_893_, v_a_894_, v_b_895_);
lean_dec_ref(v_a_893_);
lean_dec(v___x_892_);
lean_dec_ref(v___x_891_);
return v_res_896_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__3));
v___x_906_ = l_Lean_MessageData_ofFormat(v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(lean_object* v_x_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v_a_912_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1));
v___x_923_ = l_Lean_Syntax_isLit_x3f(v___x_922_, v_x_907_);
if (lean_obj_tag(v___x_923_) == 1)
{
lean_object* v_val_924_; 
lean_dec_ref(v_a_908_);
v_val_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_val_924_);
lean_dec_ref(v___x_923_);
v_a_912_ = v_val_924_;
goto v___jp_911_;
}
else
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec(v___x_923_);
v___x_925_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4);
v___x_926_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_907_, v___x_925_, v_a_908_, v_a_909_);
v_a_927_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_926_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_926_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
v___jp_911_:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_913_ = lean_unsigned_to_nat(0u);
v___x_914_ = lean_unsigned_to_nat(2u);
v___x_915_ = lean_string_utf8_byte_size(v_a_912_);
lean_inc_ref(v_a_912_);
v___x_916_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_916_, 0, v_a_912_);
lean_ctor_set(v___x_916_, 1, v___x_913_);
lean_ctor_set(v___x_916_, 2, v___x_915_);
v___x_917_ = l_String_Slice_Pos_nextn(v___x_916_, v___x_913_, v___x_914_);
lean_dec_ref(v___x_916_);
lean_inc(v___x_917_);
lean_inc_ref(v_a_912_);
v___x_918_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_918_, 0, v_a_912_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
lean_ctor_set(v___x_918_, 2, v___x_915_);
v___x_919_ = l_String_Slice_positions(v___x_918_);
v___x_920_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_918_, v___x_917_, v_a_912_, v___x_919_, v___x_913_);
lean_dec_ref(v_a_912_);
lean_dec(v___x_917_);
lean_dec_ref(v___x_918_);
v___x_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
return v___x_921_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___boxed(lean_object* v_x_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(v_x_935_, v_a_936_, v_a_937_);
lean_dec(v_a_937_);
lean_dec(v_x_935_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(lean_object* v___x_940_, lean_object* v___x_941_, lean_object* v_a_942_, lean_object* v_inst_943_, lean_object* v_R_944_, lean_object* v_a_945_, lean_object* v_b_946_, lean_object* v_c_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_940_, v___x_941_, v_a_942_, v_a_945_, v_b_946_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___boxed(lean_object* v___x_949_, lean_object* v___x_950_, lean_object* v_a_951_, lean_object* v_inst_952_, lean_object* v_R_953_, lean_object* v_a_954_, lean_object* v_b_955_, lean_object* v_c_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(v___x_949_, v___x_950_, v_a_951_, v_inst_952_, v_R_953_, v_a_954_, v_b_955_, v_c_956_);
lean_dec_ref(v_a_951_);
lean_dec(v___x_950_);
lean_dec_ref(v___x_949_);
return v_res_957_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0));
v___x_960_ = l_Lean_stringToMessageData(v___x_959_);
return v___x_960_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__5));
v___x_970_ = l_Lean_MessageData_ofFormat(v___x_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(lean_object* v_x_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v_a_976_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3));
v___x_989_ = l_Lean_Syntax_isLit_x3f(v___x_988_, v_x_971_);
if (lean_obj_tag(v___x_989_) == 1)
{
lean_object* v_val_990_; 
v_val_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_val_990_);
lean_dec_ref(v___x_989_);
v_a_976_ = v_val_990_;
goto v___jp_975_;
}
else
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec(v___x_989_);
v___x_991_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6);
v___x_992_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_971_, v___x_991_, v_a_972_, v_a_973_);
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
v___jp_975_:
{
lean_object* v___x_977_; 
v___x_977_ = l_Lake_Toml_DateTime_ofString_x3f(v_a_976_);
if (lean_obj_tag(v___x_977_) == 1)
{
lean_object* v_val_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec_ref(v_a_972_);
v_val_978_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_977_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_val_978_);
lean_dec(v___x_977_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
lean_ctor_set_tag(v___x_980_, 0);
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_val_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; 
lean_dec(v___x_977_);
v___x_986_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1);
v___x_987_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_971_, v___x_986_, v_a_972_, v_a_973_);
return v___x_987_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___boxed(lean_object* v_x_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(v_x_1001_, v_a_1002_, v_a_1003_);
lean_dec(v_a_1003_);
lean_dec(v_x_1001_);
return v_res_1005_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__3));
v___x_1015_ = l_Lean_MessageData_ofFormat(v___x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(lean_object* v_x_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v_a_1021_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
v___x_1034_ = l_Lean_Syntax_isLit_x3f(v___x_1033_, v_x_1016_);
if (lean_obj_tag(v___x_1034_) == 1)
{
lean_object* v_val_1035_; 
lean_dec_ref(v_a_1017_);
v_val_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_val_1035_);
lean_dec_ref(v___x_1034_);
v_a_1021_ = v_val_1035_;
goto v___jp_1020_;
}
else
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
lean_dec(v___x_1034_);
v___x_1036_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4);
v___x_1037_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1016_, v___x_1036_, v_a_1017_, v_a_1018_);
return v___x_1037_;
}
v___jp_1020_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1022_ = lean_unsigned_to_nat(1u);
v___x_1023_ = lean_unsigned_to_nat(0u);
v___x_1024_ = lean_string_utf8_byte_size(v_a_1021_);
lean_inc_ref(v_a_1021_);
v___x_1025_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1025_, 0, v_a_1021_);
lean_ctor_set(v___x_1025_, 1, v___x_1023_);
lean_ctor_set(v___x_1025_, 2, v___x_1024_);
v___x_1026_ = l_String_Slice_Pos_nextn(v___x_1025_, v___x_1023_, v___x_1022_);
lean_dec_ref(v___x_1025_);
lean_inc(v___x_1026_);
lean_inc_ref(v_a_1021_);
v___x_1027_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1027_, 0, v_a_1021_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
lean_ctor_set(v___x_1027_, 2, v___x_1024_);
v___x_1028_ = lean_nat_sub(v___x_1024_, v___x_1026_);
v___x_1029_ = l_String_Slice_Pos_prevn(v___x_1027_, v___x_1028_, v___x_1022_);
lean_dec_ref(v___x_1027_);
v___x_1030_ = lean_nat_add(v___x_1026_, v___x_1029_);
lean_dec(v___x_1029_);
v___x_1031_ = lean_string_utf8_extract(v_a_1021_, v___x_1026_, v___x_1030_);
lean_dec(v___x_1030_);
lean_dec(v___x_1026_);
lean_dec_ref(v_a_1021_);
v___x_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
return v___x_1032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___boxed(lean_object* v_x_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(v_x_1038_, v_a_1039_, v_a_1040_);
lean_dec(v_a_1040_);
lean_dec(v_x_1038_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(lean_object* v_msg_1043_){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = l_String_instInhabitedSlice;
v___x_1045_ = lean_panic_fn(v___x_1044_, v_msg_1043_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(lean_object* v___y_1046_, lean_object* v_a_1047_, lean_object* v_b_1048_){
_start:
{
lean_object* v_str_1049_; lean_object* v_startInclusive_1050_; lean_object* v_endExclusive_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
v_str_1049_ = lean_ctor_get(v___y_1046_, 0);
v_startInclusive_1050_ = lean_ctor_get(v___y_1046_, 1);
v_endExclusive_1051_ = lean_ctor_get(v___y_1046_, 2);
v___x_1052_ = lean_nat_sub(v_endExclusive_1051_, v_startInclusive_1050_);
v___x_1053_ = lean_nat_dec_eq(v_a_1047_, v___x_1052_);
lean_dec(v___x_1052_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; uint32_t v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1054_ = lean_nat_add(v_startInclusive_1050_, v_a_1047_);
lean_dec(v_a_1047_);
v___x_1055_ = lean_string_utf8_next_fast(v_str_1049_, v___x_1054_);
v___x_1056_ = lean_nat_sub(v___x_1055_, v_startInclusive_1050_);
v___x_1057_ = lean_string_utf8_get_fast(v_str_1049_, v___x_1054_);
lean_dec(v___x_1054_);
v___x_1058_ = lean_unsigned_to_nat(16u);
v___x_1059_ = lean_nat_mul(v_b_1048_, v___x_1058_);
lean_dec(v_b_1048_);
v___x_1060_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v___x_1057_);
v___x_1061_ = lean_nat_add(v___x_1059_, v___x_1060_);
lean_dec(v___x_1060_);
lean_dec(v___x_1059_);
v_a_1047_ = v___x_1056_;
v_b_1048_ = v___x_1061_;
goto _start;
}
else
{
lean_dec(v_a_1047_);
return v_b_1048_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg___boxed(lean_object* v___y_1063_, lean_object* v_a_1064_, lean_object* v_b_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_1063_, v_a_1064_, v_b_1065_);
lean_dec_ref(v___y_1063_);
return v_res_1066_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1070_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2));
v___x_1071_ = lean_unsigned_to_nat(14u);
v___x_1072_ = lean_unsigned_to_nat(22u);
v___x_1073_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1));
v___x_1074_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0));
v___x_1075_ = l_mkPanicMessageWithDecl(v___x_1074_, v___x_1073_, v___x_1072_, v___x_1071_, v___x_1070_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits(lean_object* v_s_1076_){
_start:
{
lean_object* v_str_1077_; lean_object* v_startPos_1078_; lean_object* v_stopPos_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1097_; 
v_str_1077_ = lean_ctor_get(v_s_1076_, 0);
v_startPos_1078_ = lean_ctor_get(v_s_1076_, 1);
v_stopPos_1079_ = lean_ctor_get(v_s_1076_, 2);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_s_1076_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1081_ = v_s_1076_;
v_isShared_1082_ = v_isSharedCheck_1097_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_stopPos_1079_);
lean_inc(v_startPos_1078_);
lean_inc(v_str_1077_);
lean_dec(v_s_1076_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1097_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; lean_object* v___y_1085_; uint8_t v___x_1091_; 
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1091_ = lean_string_is_valid_pos(v_str_1077_, v_startPos_1078_);
if (v___x_1091_ == 0)
{
lean_del_object(v___x_1081_);
lean_dec(v_stopPos_1079_);
lean_dec(v_startPos_1078_);
lean_dec_ref(v_str_1077_);
goto v___jp_1088_;
}
else
{
uint8_t v___x_1092_; 
v___x_1092_ = lean_string_is_valid_pos(v_str_1077_, v_stopPos_1079_);
if (v___x_1092_ == 0)
{
lean_del_object(v___x_1081_);
lean_dec(v_stopPos_1079_);
lean_dec(v_startPos_1078_);
lean_dec_ref(v_str_1077_);
goto v___jp_1088_;
}
else
{
uint8_t v___x_1093_; 
v___x_1093_ = lean_nat_dec_le(v_startPos_1078_, v_stopPos_1079_);
if (v___x_1093_ == 0)
{
lean_del_object(v___x_1081_);
lean_dec(v_stopPos_1079_);
lean_dec(v_startPos_1078_);
lean_dec_ref(v_str_1077_);
goto v___jp_1088_;
}
else
{
lean_object* v___x_1095_; 
if (v_isShared_1082_ == 0)
{
v___x_1095_ = v___x_1081_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_str_1077_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_startPos_1078_);
lean_ctor_set(v_reuseFailAlloc_1096_, 2, v_stopPos_1079_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
v___y_1085_ = v___x_1095_;
goto v___jp_1084_;
}
}
}
}
v___jp_1084_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = l_String_Slice_positions(v___y_1085_);
v___x_1087_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_1085_, v___x_1086_, v___x_1083_);
lean_dec_ref(v___y_1085_);
return v___x_1087_;
}
v___jp_1088_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3);
v___x_1090_ = l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(v___x_1089_);
v___y_1085_ = v___x_1090_;
goto v___jp_1084_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0(lean_object* v___y_1098_, lean_object* v_inst_1099_, lean_object* v_R_1100_, lean_object* v_a_1101_, lean_object* v_b_1102_, lean_object* v_c_1103_){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_1098_, v_a_1101_, v_b_1102_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___boxed(lean_object* v___y_1105_, lean_object* v_inst_1106_, lean_object* v_R_1107_, lean_object* v_a_1108_, lean_object* v_b_1109_, lean_object* v_c_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0(v___y_1105_, v_inst_1106_, v_R_1107_, v_a_1108_, v_b_1109_, v_c_1110_);
lean_dec_ref(v___y_1105_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(lean_object* v_s_1112_, lean_object* v_stopPos_1113_, lean_object* v_i_1114_){
_start:
{
uint8_t v___y_1119_; uint8_t v___x_1120_; 
v___x_1120_ = lean_nat_dec_lt(v_i_1114_, v_stopPos_1113_);
if (v___x_1120_ == 0)
{
return v_i_1114_;
}
else
{
uint32_t v___x_1121_; uint8_t v___y_1123_; uint32_t v___x_1128_; uint8_t v___x_1129_; 
v___x_1121_ = lean_string_utf8_get(v_s_1112_, v_i_1114_);
v___x_1128_ = 32;
v___x_1129_ = lean_uint32_dec_eq(v___x_1121_, v___x_1128_);
if (v___x_1129_ == 0)
{
uint32_t v___x_1130_; uint8_t v___x_1131_; 
v___x_1130_ = 9;
v___x_1131_ = lean_uint32_dec_eq(v___x_1121_, v___x_1130_);
v___y_1123_ = v___x_1131_;
goto v___jp_1122_;
}
else
{
v___y_1123_ = v___x_1129_;
goto v___jp_1122_;
}
v___jp_1122_:
{
if (v___y_1123_ == 0)
{
uint32_t v___x_1124_; uint8_t v___x_1125_; 
v___x_1124_ = 13;
v___x_1125_ = lean_uint32_dec_eq(v___x_1121_, v___x_1124_);
if (v___x_1125_ == 0)
{
uint32_t v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = 10;
v___x_1127_ = lean_uint32_dec_eq(v___x_1121_, v___x_1126_);
v___y_1119_ = v___x_1127_;
goto v___jp_1118_;
}
else
{
v___y_1119_ = v___x_1125_;
goto v___jp_1118_;
}
}
else
{
goto v___jp_1115_;
}
}
}
v___jp_1115_:
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_string_utf8_next(v_s_1112_, v_i_1114_);
lean_dec(v_i_1114_);
v_i_1114_ = v___x_1116_;
goto _start;
}
v___jp_1118_:
{
if (v___y_1119_ == 0)
{
return v_i_1114_;
}
else
{
goto v___jp_1115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0___boxed(lean_object* v_s_1132_, lean_object* v_stopPos_1133_, lean_object* v_i_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(v_s_1132_, v_stopPos_1133_, v_i_1134_);
lean_dec(v_stopPos_1133_);
lean_dec_ref(v_s_1132_);
return v_res_1135_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0));
v___x_1138_ = l_Lean_stringToMessageData(v___x_1137_);
return v___x_1138_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2));
v___x_1141_ = l_Lean_stringToMessageData(v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(lean_object* v_lit_1142_, lean_object* v_i_1143_, lean_object* v_out_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v_escape_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; uint8_t v___x_1180_; 
v___x_1180_ = lean_string_utf8_at_end(v_lit_1142_, v_i_1143_);
if (v___x_1180_ == 0)
{
uint32_t v_curr_1181_; lean_object* v_i_1182_; uint32_t v___x_1183_; uint8_t v___x_1184_; 
v_curr_1181_ = lean_string_utf8_get_fast(v_lit_1142_, v_i_1143_);
v_i_1182_ = lean_string_utf8_next_fast(v_lit_1142_, v_i_1143_);
lean_dec(v_i_1143_);
v___x_1183_ = 92;
v___x_1184_ = lean_uint32_dec_eq(v_curr_1181_, v___x_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; 
v___x_1185_ = lean_string_push(v_out_1144_, v_curr_1181_);
v_i_1143_ = v_i_1182_;
v_out_1144_ = v___x_1185_;
goto _start;
}
else
{
uint8_t v___x_1187_; 
v___x_1187_ = lean_string_utf8_at_end(v_lit_1142_, v_i_1182_);
if (v___x_1187_ == 0)
{
uint32_t v_curr_1188_; lean_object* v_next_1189_; uint32_t v___x_1190_; uint8_t v___x_1191_; 
v_curr_1188_ = lean_string_utf8_get_fast(v_lit_1142_, v_i_1182_);
v_next_1189_ = lean_string_utf8_next_fast(v_lit_1142_, v_i_1182_);
v___x_1190_ = 98;
v___x_1191_ = lean_uint32_dec_eq(v_curr_1188_, v___x_1190_);
if (v___x_1191_ == 0)
{
uint32_t v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = 116;
v___x_1193_ = lean_uint32_dec_eq(v_curr_1188_, v___x_1192_);
if (v___x_1193_ == 0)
{
uint32_t v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = 110;
v___x_1195_ = lean_uint32_dec_eq(v_curr_1188_, v___x_1194_);
if (v___x_1195_ == 0)
{
uint32_t v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = 102;
v___x_1197_ = lean_uint32_dec_eq(v_curr_1188_, v___x_1196_);
if (v___x_1197_ == 0)
{
uint32_t v___x_1198_; uint8_t v___x_1199_; 
v___x_1198_ = 114;
v___x_1199_ = lean_uint32_dec_eq(v_curr_1188_, v___x_1198_);
if (v___x_1199_ == 0)
{
uint32_t v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = 34;
v___x_1201_ = lean_uint32_dec_eq(v_curr_1188_, v___x_1200_);
if (v___x_1201_ == 0)
{
uint8_t v___x_1202_; 
v___x_1202_ = lean_uint32_dec_eq(v_curr_1188_, v___x_1183_);
if (v___x_1202_ == 0)
{
uint32_t v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = 117;
v___x_1204_ = lean_uint32_dec_eq(v_curr_1188_, v___x_1203_);
if (v___x_1204_ == 0)
{
uint32_t v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = 85;
v___x_1206_ = lean_uint32_dec_eq(v_curr_1188_, v___x_1205_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; lean_object* v_b_1208_; 
v___x_1207_ = lean_string_utf8_byte_size(v_lit_1142_);
v_b_1208_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(v_lit_1142_, v___x_1207_, v_i_1182_);
v_i_1143_ = v_b_1208_;
goto _start;
}
else
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1210_ = lean_string_utf8_byte_size(v_lit_1142_);
lean_inc_ref(v_lit_1142_);
v___x_1211_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1211_, 0, v_lit_1142_);
lean_ctor_set(v___x_1211_, 1, v_next_1189_);
lean_ctor_set(v___x_1211_, 2, v___x_1210_);
v___x_1212_ = lean_unsigned_to_nat(8u);
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = l_Substring_Raw_nextn(v___x_1211_, v___x_1212_, v___x_1213_);
lean_dec_ref(v___x_1211_);
v___x_1215_ = lean_nat_add(v_next_1189_, v___x_1214_);
lean_dec(v___x_1214_);
lean_inc_ref(v_lit_1142_);
v___x_1216_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1216_, 0, v_lit_1142_);
lean_ctor_set(v___x_1216_, 1, v_next_1189_);
lean_ctor_set(v___x_1216_, 2, v___x_1215_);
v_escape_1170_ = v___x_1216_;
v___y_1171_ = v_a_1145_;
v___y_1172_ = v_a_1146_;
goto v___jp_1169_;
}
}
else
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1217_ = lean_string_utf8_byte_size(v_lit_1142_);
lean_inc_ref(v_lit_1142_);
v___x_1218_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1218_, 0, v_lit_1142_);
lean_ctor_set(v___x_1218_, 1, v_next_1189_);
lean_ctor_set(v___x_1218_, 2, v___x_1217_);
v___x_1219_ = lean_unsigned_to_nat(4u);
v___x_1220_ = lean_unsigned_to_nat(0u);
v___x_1221_ = l_Substring_Raw_nextn(v___x_1218_, v___x_1219_, v___x_1220_);
lean_dec_ref(v___x_1218_);
v___x_1222_ = lean_nat_add(v_next_1189_, v___x_1221_);
lean_dec(v___x_1221_);
lean_inc_ref(v_lit_1142_);
v___x_1223_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1223_, 0, v_lit_1142_);
lean_ctor_set(v___x_1223_, 1, v_next_1189_);
lean_ctor_set(v___x_1223_, 2, v___x_1222_);
v_escape_1170_ = v___x_1223_;
v___y_1171_ = v_a_1145_;
v___y_1172_ = v_a_1146_;
goto v___jp_1169_;
}
}
else
{
lean_object* v___x_1224_; 
v___x_1224_ = lean_string_push(v_out_1144_, v___x_1183_);
v_i_1143_ = v_next_1189_;
v_out_1144_ = v___x_1224_;
goto _start;
}
}
else
{
lean_object* v___x_1226_; 
v___x_1226_ = lean_string_push(v_out_1144_, v___x_1200_);
v_i_1143_ = v_next_1189_;
v_out_1144_ = v___x_1226_;
goto _start;
}
}
else
{
uint32_t v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = 13;
v___x_1229_ = lean_string_push(v_out_1144_, v___x_1228_);
v_i_1143_ = v_next_1189_;
v_out_1144_ = v___x_1229_;
goto _start;
}
}
else
{
uint32_t v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = 12;
v___x_1232_ = lean_string_push(v_out_1144_, v___x_1231_);
v_i_1143_ = v_next_1189_;
v_out_1144_ = v___x_1232_;
goto _start;
}
}
else
{
uint32_t v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = 10;
v___x_1235_ = lean_string_push(v_out_1144_, v___x_1234_);
v_i_1143_ = v_next_1189_;
v_out_1144_ = v___x_1235_;
goto _start;
}
}
else
{
uint32_t v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = 9;
v___x_1238_ = lean_string_push(v_out_1144_, v___x_1237_);
v_i_1143_ = v_next_1189_;
v_out_1144_ = v___x_1238_;
goto _start;
}
}
else
{
uint32_t v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = 8;
v___x_1241_ = lean_string_push(v_out_1144_, v___x_1240_);
v_i_1143_ = v_next_1189_;
v_out_1144_ = v___x_1241_;
goto _start;
}
}
else
{
lean_object* v___x_1243_; 
lean_dec_ref(v_lit_1142_);
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v_out_1144_);
return v___x_1243_;
}
}
}
else
{
lean_object* v___x_1244_; 
lean_dec(v_i_1143_);
lean_dec_ref(v_lit_1142_);
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v_out_1144_);
return v___x_1244_;
}
v___jp_1148_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1152_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1);
v___x_1153_ = lean_substring_tostring(v___y_1150_);
v___x_1154_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
v___x_1155_ = l_Lean_MessageData_ofFormat(v___x_1154_);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1152_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
v___x_1158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v___x_1158_, v___y_1149_, v___y_1151_);
return v___x_1159_;
}
v___jp_1160_:
{
lean_object* v_stopPos_1165_; uint32_t v_ch_1166_; lean_object* v___x_1167_; 
v_stopPos_1165_ = lean_ctor_get(v___y_1163_, 2);
lean_inc(v_stopPos_1165_);
lean_dec_ref(v___y_1163_);
v_ch_1166_ = lean_uint32_of_nat(v___y_1162_);
lean_dec(v___y_1162_);
v___x_1167_ = lean_string_push(v_out_1144_, v_ch_1166_);
v_i_1143_ = v_stopPos_1165_;
v_out_1144_ = v___x_1167_;
v_a_1145_ = v___y_1161_;
v_a_1146_ = v___y_1164_;
goto _start;
}
v___jp_1169_:
{
lean_object* v_val_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
lean_inc_ref(v_escape_1170_);
v_val_1173_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits(v_escape_1170_);
v___x_1174_ = lean_unsigned_to_nat(55296u);
v___x_1175_ = lean_nat_dec_lt(v_val_1173_, v___x_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = lean_unsigned_to_nat(57343u);
v___x_1177_ = lean_nat_dec_lt(v___x_1176_, v_val_1173_);
if (v___x_1177_ == 0)
{
lean_dec(v_val_1173_);
lean_dec_ref(v_out_1144_);
lean_dec_ref(v_lit_1142_);
v___y_1149_ = v___y_1171_;
v___y_1150_ = v_escape_1170_;
v___y_1151_ = v___y_1172_;
goto v___jp_1148_;
}
else
{
lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = lean_unsigned_to_nat(1114112u);
v___x_1179_ = lean_nat_dec_lt(v_val_1173_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_dec(v_val_1173_);
lean_dec_ref(v_out_1144_);
lean_dec_ref(v_lit_1142_);
v___y_1149_ = v___y_1171_;
v___y_1150_ = v_escape_1170_;
v___y_1151_ = v___y_1172_;
goto v___jp_1148_;
}
else
{
v___y_1161_ = v___y_1171_;
v___y_1162_ = v_val_1173_;
v___y_1163_ = v_escape_1170_;
v___y_1164_ = v___y_1172_;
goto v___jp_1160_;
}
}
}
else
{
v___y_1161_ = v___y_1171_;
v___y_1162_ = v_val_1173_;
v___y_1163_ = v_escape_1170_;
v___y_1164_ = v___y_1172_;
goto v___jp_1160_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___boxed(lean_object* v_lit_1245_, lean_object* v_i_1246_, lean_object* v_out_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(v_lit_1245_, v_i_1246_, v_out_1247_, v_a_1248_, v_a_1249_);
lean_dec(v_a_1249_);
lean_dec_ref(v_a_1248_);
return v_res_1251_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__4));
v___x_1262_ = l_Lean_MessageData_ofFormat(v___x_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(lean_object* v_x_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_){
_start:
{
lean_object* v_a_1268_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
v___x_1306_ = l_Lean_Syntax_isLit_x3f(v___x_1305_, v_x_1263_);
if (lean_obj_tag(v___x_1306_) == 1)
{
lean_object* v_val_1307_; 
v_val_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_val_1307_);
lean_dec_ref(v___x_1306_);
v_a_1268_ = v_val_1307_;
goto v___jp_1267_;
}
else
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
lean_dec(v___x_1306_);
v___x_1308_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5);
v___x_1309_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1263_, v___x_1308_, v_a_1264_, v_a_1265_);
return v___x_1309_;
}
v___jp_1267_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v_fileName_1272_; lean_object* v_fileMap_1273_; lean_object* v_options_1274_; lean_object* v_currRecDepth_1275_; lean_object* v_maxRecDepth_1276_; lean_object* v_ref_1277_; lean_object* v_currNamespace_1278_; lean_object* v_openDecls_1279_; lean_object* v_initHeartbeats_1280_; lean_object* v_maxHeartbeats_1281_; lean_object* v_quotContext_1282_; lean_object* v_currMacroScope_1283_; uint8_t v_diag_1284_; lean_object* v_cancelTk_x3f_1285_; uint8_t v_suppressElabErrors_1286_; lean_object* v_inheritedTraceOptions_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1304_; 
v___x_1269_ = lean_unsigned_to_nat(0u);
v___x_1270_ = lean_string_utf8_byte_size(v_a_1268_);
lean_inc_ref(v_a_1268_);
v___x_1271_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1271_, 0, v_a_1268_);
lean_ctor_set(v___x_1271_, 1, v___x_1269_);
lean_ctor_set(v___x_1271_, 2, v___x_1270_);
v_fileName_1272_ = lean_ctor_get(v_a_1264_, 0);
v_fileMap_1273_ = lean_ctor_get(v_a_1264_, 1);
v_options_1274_ = lean_ctor_get(v_a_1264_, 2);
v_currRecDepth_1275_ = lean_ctor_get(v_a_1264_, 3);
v_maxRecDepth_1276_ = lean_ctor_get(v_a_1264_, 4);
v_ref_1277_ = lean_ctor_get(v_a_1264_, 5);
v_currNamespace_1278_ = lean_ctor_get(v_a_1264_, 6);
v_openDecls_1279_ = lean_ctor_get(v_a_1264_, 7);
v_initHeartbeats_1280_ = lean_ctor_get(v_a_1264_, 8);
v_maxHeartbeats_1281_ = lean_ctor_get(v_a_1264_, 9);
v_quotContext_1282_ = lean_ctor_get(v_a_1264_, 10);
v_currMacroScope_1283_ = lean_ctor_get(v_a_1264_, 11);
v_diag_1284_ = lean_ctor_get_uint8(v_a_1264_, sizeof(void*)*14);
v_cancelTk_x3f_1285_ = lean_ctor_get(v_a_1264_, 12);
v_suppressElabErrors_1286_ = lean_ctor_get_uint8(v_a_1264_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1287_ = lean_ctor_get(v_a_1264_, 13);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_a_1264_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1289_ = v_a_1264_;
v_isShared_1290_ = v_isSharedCheck_1304_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_inheritedTraceOptions_1287_);
lean_inc(v_cancelTk_x3f_1285_);
lean_inc(v_currMacroScope_1283_);
lean_inc(v_quotContext_1282_);
lean_inc(v_maxHeartbeats_1281_);
lean_inc(v_initHeartbeats_1280_);
lean_inc(v_openDecls_1279_);
lean_inc(v_currNamespace_1278_);
lean_inc(v_ref_1277_);
lean_inc(v_maxRecDepth_1276_);
lean_inc(v_currRecDepth_1275_);
lean_inc(v_options_1274_);
lean_inc(v_fileMap_1273_);
lean_inc(v_fileName_1272_);
lean_dec(v_a_1264_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1304_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v_ref_1299_; lean_object* v___x_1301_; 
v___x_1291_ = lean_unsigned_to_nat(1u);
v___x_1292_ = l_String_Slice_Pos_nextn(v___x_1271_, v___x_1269_, v___x_1291_);
lean_dec_ref(v___x_1271_);
lean_inc(v___x_1292_);
lean_inc_ref(v_a_1268_);
v___x_1293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1293_, 0, v_a_1268_);
lean_ctor_set(v___x_1293_, 1, v___x_1292_);
lean_ctor_set(v___x_1293_, 2, v___x_1270_);
v___x_1294_ = lean_nat_sub(v___x_1270_, v___x_1292_);
v___x_1295_ = l_String_Slice_Pos_prevn(v___x_1293_, v___x_1294_, v___x_1291_);
lean_dec_ref(v___x_1293_);
v___x_1296_ = lean_nat_add(v___x_1292_, v___x_1295_);
lean_dec(v___x_1295_);
v___x_1297_ = lean_string_utf8_extract(v_a_1268_, v___x_1292_, v___x_1296_);
lean_dec(v___x_1296_);
lean_dec(v___x_1292_);
lean_dec_ref(v_a_1268_);
v___x_1298_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0));
v_ref_1299_ = l_Lean_replaceRef(v_x_1263_, v_ref_1277_);
lean_dec(v_ref_1277_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 5, v_ref_1299_);
v___x_1301_ = v___x_1289_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_fileName_1272_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_fileMap_1273_);
lean_ctor_set(v_reuseFailAlloc_1303_, 2, v_options_1274_);
lean_ctor_set(v_reuseFailAlloc_1303_, 3, v_currRecDepth_1275_);
lean_ctor_set(v_reuseFailAlloc_1303_, 4, v_maxRecDepth_1276_);
lean_ctor_set(v_reuseFailAlloc_1303_, 5, v_ref_1299_);
lean_ctor_set(v_reuseFailAlloc_1303_, 6, v_currNamespace_1278_);
lean_ctor_set(v_reuseFailAlloc_1303_, 7, v_openDecls_1279_);
lean_ctor_set(v_reuseFailAlloc_1303_, 8, v_initHeartbeats_1280_);
lean_ctor_set(v_reuseFailAlloc_1303_, 9, v_maxHeartbeats_1281_);
lean_ctor_set(v_reuseFailAlloc_1303_, 10, v_quotContext_1282_);
lean_ctor_set(v_reuseFailAlloc_1303_, 11, v_currMacroScope_1283_);
lean_ctor_set(v_reuseFailAlloc_1303_, 12, v_cancelTk_x3f_1285_);
lean_ctor_set(v_reuseFailAlloc_1303_, 13, v_inheritedTraceOptions_1287_);
lean_ctor_set_uint8(v_reuseFailAlloc_1303_, sizeof(void*)*14, v_diag_1284_);
lean_ctor_set_uint8(v_reuseFailAlloc_1303_, sizeof(void*)*14 + 1, v_suppressElabErrors_1286_);
v___x_1301_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1302_; 
v___x_1302_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(v___x_1297_, v___x_1269_, v___x_1298_, v___x_1301_, v_a_1265_);
lean_dec_ref(v___x_1301_);
return v___x_1302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___boxed(lean_object* v_x_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(v_x_1310_, v_a_1311_, v_a_1312_);
lean_dec(v_a_1312_);
lean_dec(v_x_1310_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(lean_object* v_s_1315_){
_start:
{
uint32_t v___y_1317_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1334_ = lean_unsigned_to_nat(0u);
v___x_1335_ = lean_string_utf8_byte_size(v_s_1315_);
lean_inc_ref(v_s_1315_);
v___x_1336_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1336_, 0, v_s_1315_);
lean_ctor_set(v___x_1336_, 1, v___x_1334_);
lean_ctor_set(v___x_1336_, 2, v___x_1335_);
v___x_1337_ = l_String_Slice_Pos_get_x3f(v___x_1336_, v___x_1334_);
lean_dec_ref(v___x_1336_);
if (lean_obj_tag(v___x_1337_) == 0)
{
uint32_t v___x_1338_; 
v___x_1338_ = 65;
v___y_1317_ = v___x_1338_;
goto v___jp_1316_;
}
else
{
lean_object* v_val_1339_; uint32_t v___x_1340_; 
v_val_1339_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_val_1339_);
lean_dec_ref(v___x_1337_);
v___x_1340_ = lean_unbox_uint32(v_val_1339_);
lean_dec(v_val_1339_);
v___y_1317_ = v___x_1340_;
goto v___jp_1316_;
}
v___jp_1316_:
{
uint32_t v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = 13;
v___x_1319_ = lean_uint32_dec_eq(v___y_1317_, v___x_1318_);
if (v___x_1319_ == 0)
{
uint32_t v___x_1320_; uint8_t v___x_1321_; 
v___x_1320_ = 10;
v___x_1321_ = lean_uint32_dec_eq(v___y_1317_, v___x_1320_);
if (v___x_1321_ == 0)
{
return v_s_1315_;
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1322_ = lean_unsigned_to_nat(1u);
v___x_1323_ = lean_unsigned_to_nat(0u);
v___x_1324_ = lean_string_utf8_byte_size(v_s_1315_);
lean_inc_ref(v_s_1315_);
v___x_1325_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1325_, 0, v_s_1315_);
lean_ctor_set(v___x_1325_, 1, v___x_1323_);
lean_ctor_set(v___x_1325_, 2, v___x_1324_);
v___x_1326_ = l_String_Slice_Pos_nextn(v___x_1325_, v___x_1323_, v___x_1322_);
lean_dec_ref(v___x_1325_);
v___x_1327_ = lean_string_utf8_extract(v_s_1315_, v___x_1326_, v___x_1324_);
lean_dec(v___x_1326_);
lean_dec_ref(v_s_1315_);
return v___x_1327_;
}
}
else
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1328_ = lean_unsigned_to_nat(2u);
v___x_1329_ = lean_unsigned_to_nat(0u);
v___x_1330_ = lean_string_utf8_byte_size(v_s_1315_);
lean_inc_ref(v_s_1315_);
v___x_1331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1331_, 0, v_s_1315_);
lean_ctor_set(v___x_1331_, 1, v___x_1329_);
lean_ctor_set(v___x_1331_, 2, v___x_1330_);
v___x_1332_ = l_String_Slice_Pos_nextn(v___x_1331_, v___x_1329_, v___x_1328_);
lean_dec_ref(v___x_1331_);
v___x_1333_ = lean_string_utf8_extract(v_s_1315_, v___x_1332_, v___x_1330_);
lean_dec(v___x_1332_);
lean_dec_ref(v_s_1315_);
return v___x_1333_;
}
}
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4(void){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__3));
v___x_1350_ = l_Lean_MessageData_ofFormat(v___x_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(lean_object* v_x_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v_a_1356_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1));
v___x_1370_ = l_Lean_Syntax_isLit_x3f(v___x_1369_, v_x_1351_);
if (lean_obj_tag(v___x_1370_) == 1)
{
lean_object* v_val_1371_; 
lean_dec_ref(v_a_1352_);
v_val_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_val_1371_);
lean_dec_ref(v___x_1370_);
v_a_1356_ = v_val_1371_;
goto v___jp_1355_;
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
lean_dec(v___x_1370_);
v___x_1372_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4);
v___x_1373_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1351_, v___x_1372_, v_a_1352_, v_a_1353_);
return v___x_1373_;
}
v___jp_1355_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1357_ = lean_unsigned_to_nat(3u);
v___x_1358_ = lean_unsigned_to_nat(0u);
v___x_1359_ = lean_string_utf8_byte_size(v_a_1356_);
lean_inc_ref(v_a_1356_);
v___x_1360_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1360_, 0, v_a_1356_);
lean_ctor_set(v___x_1360_, 1, v___x_1358_);
lean_ctor_set(v___x_1360_, 2, v___x_1359_);
v___x_1361_ = l_String_Slice_Pos_nextn(v___x_1360_, v___x_1358_, v___x_1357_);
lean_dec_ref(v___x_1360_);
lean_inc(v___x_1361_);
lean_inc_ref(v_a_1356_);
v___x_1362_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1362_, 0, v_a_1356_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
lean_ctor_set(v___x_1362_, 2, v___x_1359_);
v___x_1363_ = lean_nat_sub(v___x_1359_, v___x_1361_);
v___x_1364_ = l_String_Slice_Pos_prevn(v___x_1362_, v___x_1363_, v___x_1357_);
lean_dec_ref(v___x_1362_);
v___x_1365_ = lean_nat_add(v___x_1361_, v___x_1364_);
lean_dec(v___x_1364_);
v___x_1366_ = lean_string_utf8_extract(v_a_1356_, v___x_1361_, v___x_1365_);
lean_dec(v___x_1365_);
lean_dec(v___x_1361_);
lean_dec_ref(v_a_1356_);
v___x_1367_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(v___x_1366_);
v___x_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
return v___x_1368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___boxed(lean_object* v_x_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(v_x_1374_, v_a_1375_, v_a_1376_);
lean_dec(v_a_1376_);
lean_dec(v_x_1374_);
return v_res_1378_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4(void){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__3));
v___x_1388_ = l_Lean_MessageData_ofFormat(v___x_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(lean_object* v_x_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_){
_start:
{
lean_object* v_a_1394_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1));
v___x_1433_ = l_Lean_Syntax_isLit_x3f(v___x_1432_, v_x_1389_);
if (lean_obj_tag(v___x_1433_) == 1)
{
lean_object* v_val_1434_; 
v_val_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_val_1434_);
lean_dec_ref(v___x_1433_);
v_a_1394_ = v_val_1434_;
goto v___jp_1393_;
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_dec(v___x_1433_);
v___x_1435_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4);
v___x_1436_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1389_, v___x_1435_, v_a_1390_, v_a_1391_);
return v___x_1436_;
}
v___jp_1393_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v_fileName_1398_; lean_object* v_fileMap_1399_; lean_object* v_options_1400_; lean_object* v_currRecDepth_1401_; lean_object* v_maxRecDepth_1402_; lean_object* v_ref_1403_; lean_object* v_currNamespace_1404_; lean_object* v_openDecls_1405_; lean_object* v_initHeartbeats_1406_; lean_object* v_maxHeartbeats_1407_; lean_object* v_quotContext_1408_; lean_object* v_currMacroScope_1409_; uint8_t v_diag_1410_; lean_object* v_cancelTk_x3f_1411_; uint8_t v_suppressElabErrors_1412_; lean_object* v_inheritedTraceOptions_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1431_; 
v___x_1395_ = lean_unsigned_to_nat(0u);
v___x_1396_ = lean_string_utf8_byte_size(v_a_1394_);
lean_inc_ref(v_a_1394_);
v___x_1397_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1397_, 0, v_a_1394_);
lean_ctor_set(v___x_1397_, 1, v___x_1395_);
lean_ctor_set(v___x_1397_, 2, v___x_1396_);
v_fileName_1398_ = lean_ctor_get(v_a_1390_, 0);
v_fileMap_1399_ = lean_ctor_get(v_a_1390_, 1);
v_options_1400_ = lean_ctor_get(v_a_1390_, 2);
v_currRecDepth_1401_ = lean_ctor_get(v_a_1390_, 3);
v_maxRecDepth_1402_ = lean_ctor_get(v_a_1390_, 4);
v_ref_1403_ = lean_ctor_get(v_a_1390_, 5);
v_currNamespace_1404_ = lean_ctor_get(v_a_1390_, 6);
v_openDecls_1405_ = lean_ctor_get(v_a_1390_, 7);
v_initHeartbeats_1406_ = lean_ctor_get(v_a_1390_, 8);
v_maxHeartbeats_1407_ = lean_ctor_get(v_a_1390_, 9);
v_quotContext_1408_ = lean_ctor_get(v_a_1390_, 10);
v_currMacroScope_1409_ = lean_ctor_get(v_a_1390_, 11);
v_diag_1410_ = lean_ctor_get_uint8(v_a_1390_, sizeof(void*)*14);
v_cancelTk_x3f_1411_ = lean_ctor_get(v_a_1390_, 12);
v_suppressElabErrors_1412_ = lean_ctor_get_uint8(v_a_1390_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1413_ = lean_ctor_get(v_a_1390_, 13);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_a_1390_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1415_ = v_a_1390_;
v_isShared_1416_ = v_isSharedCheck_1431_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_inheritedTraceOptions_1413_);
lean_inc(v_cancelTk_x3f_1411_);
lean_inc(v_currMacroScope_1409_);
lean_inc(v_quotContext_1408_);
lean_inc(v_maxHeartbeats_1407_);
lean_inc(v_initHeartbeats_1406_);
lean_inc(v_openDecls_1405_);
lean_inc(v_currNamespace_1404_);
lean_inc(v_ref_1403_);
lean_inc(v_maxRecDepth_1402_);
lean_inc(v_currRecDepth_1401_);
lean_inc(v_options_1400_);
lean_inc(v_fileMap_1399_);
lean_inc(v_fileName_1398_);
lean_dec(v_a_1390_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1431_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v_ref_1426_; lean_object* v___x_1428_; 
v___x_1417_ = lean_unsigned_to_nat(3u);
v___x_1418_ = l_String_Slice_Pos_nextn(v___x_1397_, v___x_1395_, v___x_1417_);
lean_dec_ref(v___x_1397_);
lean_inc(v___x_1418_);
lean_inc_ref(v_a_1394_);
v___x_1419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1419_, 0, v_a_1394_);
lean_ctor_set(v___x_1419_, 1, v___x_1418_);
lean_ctor_set(v___x_1419_, 2, v___x_1396_);
v___x_1420_ = lean_nat_sub(v___x_1396_, v___x_1418_);
v___x_1421_ = l_String_Slice_Pos_prevn(v___x_1419_, v___x_1420_, v___x_1417_);
lean_dec_ref(v___x_1419_);
v___x_1422_ = lean_nat_add(v___x_1418_, v___x_1421_);
lean_dec(v___x_1421_);
v___x_1423_ = lean_string_utf8_extract(v_a_1394_, v___x_1418_, v___x_1422_);
lean_dec(v___x_1422_);
lean_dec(v___x_1418_);
lean_dec_ref(v_a_1394_);
v___x_1424_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(v___x_1423_);
v___x_1425_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0));
v_ref_1426_ = l_Lean_replaceRef(v_x_1389_, v_ref_1403_);
lean_dec(v_ref_1403_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 5, v_ref_1426_);
v___x_1428_ = v___x_1415_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_fileName_1398_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_fileMap_1399_);
lean_ctor_set(v_reuseFailAlloc_1430_, 2, v_options_1400_);
lean_ctor_set(v_reuseFailAlloc_1430_, 3, v_currRecDepth_1401_);
lean_ctor_set(v_reuseFailAlloc_1430_, 4, v_maxRecDepth_1402_);
lean_ctor_set(v_reuseFailAlloc_1430_, 5, v_ref_1426_);
lean_ctor_set(v_reuseFailAlloc_1430_, 6, v_currNamespace_1404_);
lean_ctor_set(v_reuseFailAlloc_1430_, 7, v_openDecls_1405_);
lean_ctor_set(v_reuseFailAlloc_1430_, 8, v_initHeartbeats_1406_);
lean_ctor_set(v_reuseFailAlloc_1430_, 9, v_maxHeartbeats_1407_);
lean_ctor_set(v_reuseFailAlloc_1430_, 10, v_quotContext_1408_);
lean_ctor_set(v_reuseFailAlloc_1430_, 11, v_currMacroScope_1409_);
lean_ctor_set(v_reuseFailAlloc_1430_, 12, v_cancelTk_x3f_1411_);
lean_ctor_set(v_reuseFailAlloc_1430_, 13, v_inheritedTraceOptions_1413_);
lean_ctor_set_uint8(v_reuseFailAlloc_1430_, sizeof(void*)*14, v_diag_1410_);
lean_ctor_set_uint8(v_reuseFailAlloc_1430_, sizeof(void*)*14 + 1, v_suppressElabErrors_1412_);
v___x_1428_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1429_; 
v___x_1429_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(v___x_1424_, v___x_1395_, v___x_1425_, v___x_1428_, v_a_1391_);
lean_dec_ref(v___x_1428_);
return v___x_1429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___boxed(lean_object* v_x_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(v_x_1437_, v_a_1438_, v_a_1439_);
lean_dec(v_a_1439_);
lean_dec(v_x_1437_);
return v_res_1441_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__2));
v___x_1449_ = l_Lean_stringToMessageData(v___x_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(lean_object* v_x_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1454_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1));
lean_inc(v_x_1450_);
v___x_1455_ = l_Lean_Syntax_isOfKind(v_x_1450_, v___x_1454_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3);
v___x_1457_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1450_, v___x_1456_, v_a_1451_, v_a_1452_);
lean_dec(v_x_1450_);
return v___x_1457_;
}
else
{
lean_object* v___x_1458_; lean_object* v_x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
v___x_1458_ = lean_unsigned_to_nat(0u);
v_x_1459_ = l_Lean_Syntax_getArg(v_x_1450_, v___x_1458_);
v___x_1460_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
lean_inc(v_x_1459_);
v___x_1461_ = l_Lean_Syntax_isOfKind(v_x_1459_, v___x_1460_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; uint8_t v___x_1463_; 
v___x_1462_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
lean_inc(v_x_1459_);
v___x_1463_ = l_Lean_Syntax_isOfKind(v_x_1459_, v___x_1462_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; uint8_t v___x_1465_; 
v___x_1464_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1));
lean_inc(v_x_1459_);
v___x_1465_ = l_Lean_Syntax_isOfKind(v_x_1459_, v___x_1464_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; uint8_t v___x_1467_; 
v___x_1466_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1));
lean_inc(v_x_1459_);
v___x_1467_ = l_Lean_Syntax_isOfKind(v_x_1459_, v___x_1466_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec(v_x_1459_);
v___x_1468_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3);
v___x_1469_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1450_, v___x_1468_, v_a_1451_, v_a_1452_);
lean_dec(v_x_1450_);
return v___x_1469_;
}
else
{
lean_object* v___x_1470_; 
lean_dec(v_x_1450_);
v___x_1470_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(v_x_1459_, v_a_1451_, v_a_1452_);
lean_dec(v_x_1459_);
return v___x_1470_;
}
}
else
{
lean_object* v___x_1471_; 
lean_dec(v_x_1450_);
v___x_1471_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(v_x_1459_, v_a_1451_, v_a_1452_);
lean_dec(v_x_1459_);
return v___x_1471_;
}
}
else
{
lean_object* v___x_1472_; 
lean_dec(v_x_1450_);
v___x_1472_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(v_x_1459_, v_a_1451_, v_a_1452_);
lean_dec(v_x_1459_);
return v___x_1472_;
}
}
else
{
lean_object* v___x_1473_; 
lean_dec(v_x_1450_);
v___x_1473_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(v_x_1459_, v_a_1451_, v_a_1452_);
lean_dec(v_x_1459_);
return v___x_1473_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___boxed(lean_object* v_x_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(v_x_1474_, v_a_1475_, v_a_1476_);
lean_dec(v_a_1476_);
return v_res_1478_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__3));
v___x_1488_ = l_Lean_MessageData_ofFormat(v___x_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey(lean_object* v_x_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_){
_start:
{
lean_object* v___x_1493_; lean_object* v_toApplicative_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1539_; 
v___x_1493_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1);
v_toApplicative_1494_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1539_ == 0)
{
lean_object* v_unused_1540_; 
v_unused_1540_ = lean_ctor_get(v___x_1493_, 1);
lean_dec(v_unused_1540_);
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1539_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_toApplicative_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1539_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v_toFunctor_1498_; lean_object* v_toSeq_1499_; lean_object* v_toSeqLeft_1500_; lean_object* v_toSeqRight_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1537_; 
v_toFunctor_1498_ = lean_ctor_get(v_toApplicative_1494_, 0);
v_toSeq_1499_ = lean_ctor_get(v_toApplicative_1494_, 2);
v_toSeqLeft_1500_ = lean_ctor_get(v_toApplicative_1494_, 3);
v_toSeqRight_1501_ = lean_ctor_get(v_toApplicative_1494_, 4);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_toApplicative_1494_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; 
v_unused_1538_ = lean_ctor_get(v_toApplicative_1494_, 1);
lean_dec(v_unused_1538_);
v___x_1503_ = v_toApplicative_1494_;
v_isShared_1504_ = v_isSharedCheck_1537_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_toSeqRight_1501_);
lean_inc(v_toSeqLeft_1500_);
lean_inc(v_toSeq_1499_);
lean_inc(v_toFunctor_1498_);
lean_dec(v_toApplicative_1494_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1537_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; lean_object* v___f_1506_; lean_object* v___f_1507_; lean_object* v___f_1508_; lean_object* v___f_1509_; lean_object* v___x_1510_; lean_object* v___f_1511_; lean_object* v___f_1512_; lean_object* v___f_1513_; lean_object* v___x_1515_; 
v___x_1505_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1));
v___f_1506_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2));
v___f_1507_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3));
lean_inc_ref(v_toFunctor_1498_);
v___f_1508_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1508_, 0, v_toFunctor_1498_);
v___f_1509_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1509_, 0, v_toFunctor_1498_);
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___f_1508_);
lean_ctor_set(v___x_1510_, 1, v___f_1509_);
v___f_1511_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1511_, 0, v_toSeqRight_1501_);
v___f_1512_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1512_, 0, v_toSeqLeft_1500_);
v___f_1513_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1513_, 0, v_toSeq_1499_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 4, v___f_1511_);
lean_ctor_set(v___x_1503_, 3, v___f_1512_);
lean_ctor_set(v___x_1503_, 2, v___f_1513_);
lean_ctor_set(v___x_1503_, 1, v___f_1506_);
lean_ctor_set(v___x_1503_, 0, v___x_1510_);
v___x_1515_ = v___x_1503_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v___f_1506_);
lean_ctor_set(v_reuseFailAlloc_1536_, 2, v___f_1513_);
lean_ctor_set(v_reuseFailAlloc_1536_, 3, v___f_1512_);
lean_ctor_set(v_reuseFailAlloc_1536_, 4, v___f_1511_);
v___x_1515_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1517_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 1, v___f_1507_);
lean_ctor_set(v___x_1496_, 0, v___x_1515_);
v___x_1517_ = v___x_1496_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1515_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v___f_1507_);
v___x_1517_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1518_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___x_1519_ = l_Lean_Core_instMonadRefCoreM;
v___x_1520_ = l_Lean_Core_instAddMessageContextCoreM;
lean_inc_ref(v___x_1517_);
v___x_1521_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_1520_, v___x_1517_);
v___x_1522_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1518_);
lean_ctor_set(v___x_1522_, 1, v___x_1519_);
lean_ctor_set(v___x_1522_, 2, v___x_1521_);
v___x_1523_ = l_Lean_Syntax_isLit_x3f(v___x_1505_, v_x_1489_);
if (lean_obj_tag(v___x_1523_) == 1)
{
lean_object* v_val_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
lean_dec_ref(v___x_1522_);
lean_dec_ref(v___x_1517_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
lean_dec(v_x_1489_);
v_val_1524_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v___x_1523_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_val_1524_);
lean_dec(v___x_1523_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set_tag(v___x_1526_, 0);
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_val_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
else
{
lean_object* v___x_1532_; lean_object* v___x_27__overap_1533_; lean_object* v___x_1534_; 
lean_dec(v___x_1523_);
v___x_1532_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4);
v___x_27__overap_1533_ = l_Lean_throwErrorAt___redArg(v___x_1517_, v___x_1522_, v_x_1489_, v___x_1532_);
v___x_1534_ = lean_apply_3(v___x_27__overap_1533_, v_a_1490_, v_a_1491_, lean_box(0));
return v___x_1534_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___boxed(lean_object* v_x_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey(v_x_1541_, v_a_1542_, v_a_1543_);
return v_res_1545_;
}
}
static lean_object* _init_l_Lake_Toml_elabSimpleKey___closed__3(void){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = ((lean_object*)(l_Lake_Toml_elabSimpleKey___closed__2));
v___x_1553_ = l_Lean_stringToMessageData(v___x_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey(lean_object* v_x_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v___x_1558_; uint8_t v___x_1559_; 
v___x_1558_ = ((lean_object*)(l_Lake_Toml_elabSimpleKey___closed__1));
lean_inc(v_x_1554_);
v___x_1559_ = l_Lean_Syntax_isOfKind(v_x_1554_, v___x_1558_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = lean_obj_once(&l_Lake_Toml_elabSimpleKey___closed__3, &l_Lake_Toml_elabSimpleKey___closed__3_once, _init_l_Lake_Toml_elabSimpleKey___closed__3);
v___x_1561_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1554_, v___x_1560_, v_a_1555_, v_a_1556_);
lean_dec(v_x_1554_);
return v___x_1561_;
}
else
{
lean_object* v___x_1562_; lean_object* v_x_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; 
v___x_1562_ = lean_unsigned_to_nat(0u);
v_x_1563_ = l_Lean_Syntax_getArg(v_x_1554_, v___x_1562_);
v___x_1564_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1));
lean_inc(v_x_1563_);
v___x_1565_ = l_Lean_Syntax_isOfKind(v_x_1563_, v___x_1564_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
lean_inc(v_x_1563_);
v___x_1567_ = l_Lean_Syntax_isOfKind(v_x_1563_, v___x_1566_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; uint8_t v___x_1569_; 
v___x_1568_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
lean_inc(v_x_1563_);
v___x_1569_ = l_Lean_Syntax_isOfKind(v_x_1563_, v___x_1568_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_dec(v_x_1563_);
v___x_1570_ = lean_obj_once(&l_Lake_Toml_elabSimpleKey___closed__3, &l_Lake_Toml_elabSimpleKey___closed__3_once, _init_l_Lake_Toml_elabSimpleKey___closed__3);
v___x_1571_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1554_, v___x_1570_, v_a_1555_, v_a_1556_);
lean_dec(v_x_1554_);
return v___x_1571_;
}
else
{
lean_object* v___x_1572_; 
lean_dec(v_x_1554_);
v___x_1572_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(v_x_1563_, v_a_1555_, v_a_1556_);
lean_dec(v_x_1563_);
return v___x_1572_;
}
}
else
{
lean_object* v___x_1573_; 
lean_dec(v_x_1554_);
v___x_1573_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(v_x_1563_, v_a_1555_, v_a_1556_);
lean_dec(v_x_1563_);
return v___x_1573_;
}
}
else
{
lean_object* v___x_1574_; 
lean_dec(v_x_1554_);
v___x_1574_ = l_Lean_Syntax_isLit_x3f(v___x_1564_, v_x_1563_);
if (lean_obj_tag(v___x_1574_) == 1)
{
lean_object* v_val_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec(v_x_1563_);
lean_dec_ref(v_a_1555_);
v_val_1575_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1574_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_val_1575_);
lean_dec(v___x_1574_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
lean_ctor_set_tag(v___x_1577_, 0);
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_val_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
else
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
lean_dec(v___x_1574_);
v___x_1583_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4);
v___x_1584_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1563_, v___x_1583_, v_a_1555_, v_a_1556_);
lean_dec(v_x_1563_);
return v___x_1584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey___boxed(lean_object* v_x_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lake_Toml_elabSimpleKey(v_x_1585_, v_a_1586_, v_a_1587_);
lean_dec(v_a_1587_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(lean_object* v_elabVal_1590_, size_t v_sz_1591_, size_t v_i_1592_, lean_object* v_bs_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
uint8_t v___x_1597_; 
v___x_1597_ = lean_usize_dec_lt(v_i_1592_, v_sz_1591_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; 
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec_ref(v_elabVal_1590_);
v___x_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1598_, 0, v_bs_1593_);
return v___x_1598_;
}
else
{
lean_object* v_v_1599_; lean_object* v___x_1600_; 
v_v_1599_ = lean_array_uget_borrowed(v_bs_1593_, v_i_1592_);
lean_inc_ref(v_elabVal_1590_);
lean_inc(v___y_1595_);
lean_inc_ref(v___y_1594_);
lean_inc(v_v_1599_);
v___x_1600_ = lean_apply_4(v_elabVal_1590_, v_v_1599_, v___y_1594_, v___y_1595_, lean_box(0));
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1602_; lean_object* v_bs_x27_1603_; size_t v___x_1604_; size_t v___x_1605_; lean_object* v___x_1606_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref(v___x_1600_);
v___x_1602_ = lean_unsigned_to_nat(0u);
v_bs_x27_1603_ = lean_array_uset(v_bs_1593_, v_i_1592_, v___x_1602_);
v___x_1604_ = ((size_t)1ULL);
v___x_1605_ = lean_usize_add(v_i_1592_, v___x_1604_);
v___x_1606_ = lean_array_uset(v_bs_x27_1603_, v_i_1592_, v_a_1601_);
v_i_1592_ = v___x_1605_;
v_bs_1593_ = v___x_1606_;
goto _start;
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec_ref(v_bs_1593_);
lean_dec_ref(v_elabVal_1590_);
v_a_1608_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1600_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1600_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg___boxed(lean_object* v_elabVal_1616_, lean_object* v_sz_1617_, lean_object* v_i_1618_, lean_object* v_bs_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
size_t v_sz_boxed_1623_; size_t v_i_boxed_1624_; lean_object* v_res_1625_; 
v_sz_boxed_1623_ = lean_unbox_usize(v_sz_1617_);
lean_dec(v_sz_1617_);
v_i_boxed_1624_ = lean_unbox_usize(v_i_1618_);
lean_dec(v_i_1618_);
v_res_1625_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_1616_, v_sz_boxed_1623_, v_i_boxed_1624_, v_bs_1619_, v___y_1620_, v___y_1621_);
return v_res_1625_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3(void){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__2));
v___x_1633_ = l_Lean_stringToMessageData(v___x_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(lean_object* v_x_1634_, lean_object* v_elabVal_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_){
_start:
{
lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1639_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1));
lean_inc(v_x_1634_);
v___x_1640_ = l_Lean_Syntax_isOfKind(v_x_1634_, v___x_1639_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
lean_dec_ref(v_elabVal_1635_);
v___x_1641_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3);
v___x_1642_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1634_, v___x_1641_, v_a_1636_, v_a_1637_);
lean_dec(v_a_1637_);
lean_dec(v_x_1634_);
return v___x_1642_;
}
else
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v_xs_1645_; lean_object* v___x_1646_; size_t v_sz_1647_; size_t v___x_1648_; lean_object* v___x_1649_; 
v___x_1643_ = lean_unsigned_to_nat(1u);
v___x_1644_ = l_Lean_Syntax_getArg(v_x_1634_, v___x_1643_);
lean_dec(v_x_1634_);
v_xs_1645_ = l_Lean_Syntax_getArgs(v___x_1644_);
lean_dec(v___x_1644_);
v___x_1646_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_1645_);
lean_dec_ref(v_xs_1645_);
v_sz_1647_ = lean_array_size(v___x_1646_);
v___x_1648_ = ((size_t)0ULL);
v___x_1649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_1635_, v_sz_1647_, v___x_1648_, v___x_1646_, v_a_1636_, v_a_1637_);
return v___x_1649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___boxed(lean_object* v_x_1650_, lean_object* v_elabVal_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(v_x_1650_, v_elabVal_1651_, v_a_1652_, v_a_1653_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray(lean_object* v_00_u03b1_1656_, lean_object* v_x_1657_, lean_object* v_elabVal_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(v_x_1657_, v_elabVal_1658_, v_a_1659_, v_a_1660_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___boxed(lean_object* v_00_u03b1_1663_, lean_object* v_x_1664_, lean_object* v_elabVal_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray(v_00_u03b1_1663_, v_x_1664_, v_elabVal_1665_, v_a_1666_, v_a_1667_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0(lean_object* v_00_u03b1_1670_, lean_object* v_elabVal_1671_, size_t v_sz_1672_, size_t v_i_1673_, lean_object* v_bs_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_1671_, v_sz_1672_, v_i_1673_, v_bs_1674_, v___y_1675_, v___y_1676_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___boxed(lean_object* v_00_u03b1_1679_, lean_object* v_elabVal_1680_, lean_object* v_sz_1681_, lean_object* v_i_1682_, lean_object* v_bs_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
size_t v_sz_boxed_1687_; size_t v_i_boxed_1688_; lean_object* v_res_1689_; 
v_sz_boxed_1687_ = lean_unbox_usize(v_sz_1681_);
lean_dec(v_sz_1681_);
v_i_boxed_1688_ = lean_unbox_usize(v_i_1682_);
lean_dec(v_i_1682_);
v_res_1689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0(v_00_u03b1_1679_, v_elabVal_1680_, v_sz_boxed_1687_, v_i_boxed_1688_, v_bs_1683_, v___y_1684_, v___y_1685_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(lean_object* v_msg_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v_ref_1694_; lean_object* v___x_1695_; lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1704_; 
v_ref_1694_ = lean_ctor_get(v___y_1691_, 5);
v___x_1695_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(v_msg_1690_, v___y_1691_, v___y_1692_);
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1698_ = v___x_1695_;
v_isShared_1699_ = v_isSharedCheck_1704_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1695_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1704_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1702_; 
lean_inc(v_ref_1694_);
v___x_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1700_, 0, v_ref_1694_);
lean_ctor_set(v___x_1700_, 1, v_a_1696_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set_tag(v___x_1698_, 1);
lean_ctor_set(v___x_1698_, 0, v___x_1700_);
v___x_1702_ = v___x_1698_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg___boxed(lean_object* v_msg_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(v_msg_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg(lean_object* v_ref_1710_, lean_object* v_msg_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_fileName_1716_; lean_object* v_fileMap_1717_; lean_object* v_options_1718_; lean_object* v_currRecDepth_1719_; lean_object* v_maxRecDepth_1720_; lean_object* v_ref_1721_; lean_object* v_currNamespace_1722_; lean_object* v_openDecls_1723_; lean_object* v_initHeartbeats_1724_; lean_object* v_maxHeartbeats_1725_; lean_object* v_quotContext_1726_; lean_object* v_currMacroScope_1727_; uint8_t v_diag_1728_; lean_object* v_cancelTk_x3f_1729_; uint8_t v_suppressElabErrors_1730_; lean_object* v_inheritedTraceOptions_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1740_; 
v_fileName_1716_ = lean_ctor_get(v___y_1713_, 0);
v_fileMap_1717_ = lean_ctor_get(v___y_1713_, 1);
v_options_1718_ = lean_ctor_get(v___y_1713_, 2);
v_currRecDepth_1719_ = lean_ctor_get(v___y_1713_, 3);
v_maxRecDepth_1720_ = lean_ctor_get(v___y_1713_, 4);
v_ref_1721_ = lean_ctor_get(v___y_1713_, 5);
v_currNamespace_1722_ = lean_ctor_get(v___y_1713_, 6);
v_openDecls_1723_ = lean_ctor_get(v___y_1713_, 7);
v_initHeartbeats_1724_ = lean_ctor_get(v___y_1713_, 8);
v_maxHeartbeats_1725_ = lean_ctor_get(v___y_1713_, 9);
v_quotContext_1726_ = lean_ctor_get(v___y_1713_, 10);
v_currMacroScope_1727_ = lean_ctor_get(v___y_1713_, 11);
v_diag_1728_ = lean_ctor_get_uint8(v___y_1713_, sizeof(void*)*14);
v_cancelTk_x3f_1729_ = lean_ctor_get(v___y_1713_, 12);
v_suppressElabErrors_1730_ = lean_ctor_get_uint8(v___y_1713_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1731_ = lean_ctor_get(v___y_1713_, 13);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___y_1713_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1733_ = v___y_1713_;
v_isShared_1734_ = v_isSharedCheck_1740_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_inheritedTraceOptions_1731_);
lean_inc(v_cancelTk_x3f_1729_);
lean_inc(v_currMacroScope_1727_);
lean_inc(v_quotContext_1726_);
lean_inc(v_maxHeartbeats_1725_);
lean_inc(v_initHeartbeats_1724_);
lean_inc(v_openDecls_1723_);
lean_inc(v_currNamespace_1722_);
lean_inc(v_ref_1721_);
lean_inc(v_maxRecDepth_1720_);
lean_inc(v_currRecDepth_1719_);
lean_inc(v_options_1718_);
lean_inc(v_fileMap_1717_);
lean_inc(v_fileName_1716_);
lean_dec(v___y_1713_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1740_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v_ref_1735_; lean_object* v___x_1737_; 
v_ref_1735_ = l_Lean_replaceRef(v_ref_1710_, v_ref_1721_);
lean_dec(v_ref_1721_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 5, v_ref_1735_);
v___x_1737_ = v___x_1733_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_fileName_1716_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_fileMap_1717_);
lean_ctor_set(v_reuseFailAlloc_1739_, 2, v_options_1718_);
lean_ctor_set(v_reuseFailAlloc_1739_, 3, v_currRecDepth_1719_);
lean_ctor_set(v_reuseFailAlloc_1739_, 4, v_maxRecDepth_1720_);
lean_ctor_set(v_reuseFailAlloc_1739_, 5, v_ref_1735_);
lean_ctor_set(v_reuseFailAlloc_1739_, 6, v_currNamespace_1722_);
lean_ctor_set(v_reuseFailAlloc_1739_, 7, v_openDecls_1723_);
lean_ctor_set(v_reuseFailAlloc_1739_, 8, v_initHeartbeats_1724_);
lean_ctor_set(v_reuseFailAlloc_1739_, 9, v_maxHeartbeats_1725_);
lean_ctor_set(v_reuseFailAlloc_1739_, 10, v_quotContext_1726_);
lean_ctor_set(v_reuseFailAlloc_1739_, 11, v_currMacroScope_1727_);
lean_ctor_set(v_reuseFailAlloc_1739_, 12, v_cancelTk_x3f_1729_);
lean_ctor_set(v_reuseFailAlloc_1739_, 13, v_inheritedTraceOptions_1731_);
lean_ctor_set_uint8(v_reuseFailAlloc_1739_, sizeof(void*)*14, v_diag_1728_);
lean_ctor_set_uint8(v_reuseFailAlloc_1739_, sizeof(void*)*14 + 1, v_suppressElabErrors_1730_);
v___x_1737_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(v_msg_1711_, v___x_1737_, v___y_1714_);
lean_dec_ref(v___x_1737_);
return v___x_1738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg___boxed(lean_object* v_ref_1741_, lean_object* v_msg_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg(v_ref_1741_, v_msg_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1743_);
lean_dec(v_ref_1741_);
return v_res_1747_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1));
v___x_1751_ = l_Lean_stringToMessageData(v___x_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(lean_object* v_t_1752_, uint8_t v___x_1753_, lean_object* v_as_1754_, size_t v_i_1755_, size_t v_stop_1756_, lean_object* v_b_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_fst_1763_; lean_object* v_snd_1764_; uint8_t v___x_1768_; 
v___x_1768_ = lean_usize_dec_eq(v_i_1755_, v_stop_1756_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = lean_array_uget_borrowed(v_as_1754_, v_i_1755_);
lean_inc_ref(v___y_1759_);
lean_inc(v___x_1769_);
v___x_1770_ = l_Lake_Toml_elabSimpleKey(v___x_1769_, v___y_1759_, v___y_1760_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1791_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref(v___x_1770_);
v___x_1772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v___x_1773_ = l_Lean_Name_str___override(v_b_1757_, v_a_1771_);
lean_inc_ref(v_t_1752_);
lean_inc(v___x_1773_);
v___x_1791_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_1772_, v___x_1773_, v_t_1752_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = lean_box(0);
lean_inc(v___x_1773_);
v___x_1793_ = l_Lake_Toml_RBDict_push___redArg(v___x_1772_, v___x_1773_, v___x_1792_, v___y_1758_);
v_fst_1763_ = v___x_1773_;
v_snd_1764_ = v___x_1793_;
goto v___jp_1762_;
}
else
{
lean_object* v_val_1794_; lean_object* v_snd_1795_; 
v_val_1794_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_val_1794_);
lean_dec_ref(v___x_1791_);
v_snd_1795_ = lean_ctor_get(v_val_1794_, 1);
lean_inc(v_snd_1795_);
lean_dec(v_val_1794_);
if (lean_obj_tag(v_snd_1795_) == 0)
{
if (v___x_1753_ == 0)
{
goto v___jp_1774_;
}
else
{
v_fst_1763_ = v___x_1773_;
v_snd_1764_ = v___y_1758_;
goto v___jp_1762_;
}
}
else
{
lean_dec_ref(v_snd_1795_);
goto v___jp_1774_;
}
}
v___jp_1774_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1775_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2);
lean_inc(v___x_1773_);
v___x_1776_ = l_Lean_MessageData_ofName(v___x_1773_);
v___x_1777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1775_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
v___x_1779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1777_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
lean_inc_ref(v___y_1759_);
v___x_1780_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg(v___x_1769_, v___x_1779_, v___y_1758_, v___y_1759_, v___y_1760_);
lean_dec_ref(v___y_1758_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v_snd_1782_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1781_);
lean_dec_ref(v___x_1780_);
v_snd_1782_ = lean_ctor_get(v_a_1781_, 1);
lean_inc(v_snd_1782_);
lean_dec(v_a_1781_);
v_fst_1763_ = v___x_1773_;
v_snd_1764_ = v_snd_1782_;
goto v___jp_1762_;
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
lean_dec(v___x_1773_);
lean_dec_ref(v___y_1759_);
lean_dec_ref(v_t_1752_);
v_a_1783_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1780_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1780_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec_ref(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v_b_1757_);
lean_dec_ref(v_t_1752_);
v_a_1796_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1770_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1770_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
else
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_dec_ref(v___y_1759_);
lean_dec_ref(v_t_1752_);
v___x_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1804_, 0, v_b_1757_);
lean_ctor_set(v___x_1804_, 1, v___y_1758_);
v___x_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
return v___x_1805_;
}
v___jp_1762_:
{
size_t v___x_1765_; size_t v___x_1766_; 
v___x_1765_ = ((size_t)1ULL);
v___x_1766_ = lean_usize_add(v_i_1755_, v___x_1765_);
v_i_1755_ = v___x_1766_;
v_b_1757_ = v_fst_1763_;
v___y_1758_ = v_snd_1764_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___boxed(lean_object* v_t_1806_, lean_object* v___x_1807_, lean_object* v_as_1808_, lean_object* v_i_1809_, lean_object* v_stop_1810_, lean_object* v_b_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
uint8_t v___x_9903__boxed_1816_; size_t v_i_boxed_1817_; size_t v_stop_boxed_1818_; lean_object* v_res_1819_; 
v___x_9903__boxed_1816_ = lean_unbox(v___x_1807_);
v_i_boxed_1817_ = lean_unbox_usize(v_i_1809_);
lean_dec(v_i_1809_);
v_stop_boxed_1818_ = lean_unbox_usize(v_stop_1810_);
lean_dec(v_stop_1810_);
v_res_1819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_t_1806_, v___x_9903__boxed_1816_, v_as_1808_, v_i_boxed_1817_, v_stop_boxed_1818_, v_b_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v_as_1808_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(size_t v_sz_1820_, size_t v_i_1821_, lean_object* v_bs_1822_){
_start:
{
uint8_t v___x_1823_; 
v___x_1823_ = lean_usize_dec_lt(v_i_1821_, v_sz_1820_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; 
v___x_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1824_, 0, v_bs_1822_);
return v___x_1824_;
}
else
{
lean_object* v_v_1825_; lean_object* v___x_1826_; lean_object* v_bs_x27_1827_; size_t v___x_1828_; size_t v___x_1829_; lean_object* v___x_1830_; 
v_v_1825_ = lean_array_uget(v_bs_1822_, v_i_1821_);
v___x_1826_ = lean_unsigned_to_nat(0u);
v_bs_x27_1827_ = lean_array_uset(v_bs_1822_, v_i_1821_, v___x_1826_);
v___x_1828_ = ((size_t)1ULL);
v___x_1829_ = lean_usize_add(v_i_1821_, v___x_1828_);
v___x_1830_ = lean_array_uset(v_bs_x27_1827_, v_i_1821_, v_v_1825_);
v_i_1821_ = v___x_1829_;
v_bs_1822_ = v___x_1830_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___boxed(lean_object* v_sz_1832_, lean_object* v_i_1833_, lean_object* v_bs_1834_){
_start:
{
size_t v_sz_boxed_1835_; size_t v_i_boxed_1836_; lean_object* v_res_1837_; 
v_sz_boxed_1835_ = lean_unbox_usize(v_sz_1832_);
lean_dec(v_sz_1832_);
v_i_boxed_1836_ = lean_unbox_usize(v_i_1833_);
lean_dec(v_i_1833_);
v_res_1837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(v_sz_boxed_1835_, v_i_boxed_1836_, v_bs_1834_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(uint8_t v___x_1838_, lean_object* v_as_1839_, size_t v_i_1840_, size_t v_stop_1841_, lean_object* v_b_1842_){
_start:
{
lean_object* v___y_1844_; uint8_t v___x_1848_; 
v___x_1848_ = lean_usize_dec_eq(v_i_1840_, v_stop_1841_);
if (v___x_1848_ == 0)
{
lean_object* v_fst_1849_; uint8_t v___x_1850_; 
v_fst_1849_ = lean_ctor_get(v_b_1842_, 0);
v___x_1850_ = lean_unbox(v_fst_1849_);
if (v___x_1850_ == 0)
{
lean_object* v_snd_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1859_; 
v_snd_1851_ = lean_ctor_get(v_b_1842_, 1);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_b_1842_);
if (v_isSharedCheck_1859_ == 0)
{
lean_object* v_unused_1860_; 
v_unused_1860_ = lean_ctor_get(v_b_1842_, 0);
lean_dec(v_unused_1860_);
v___x_1853_ = v_b_1842_;
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_snd_1851_);
lean_dec(v_b_1842_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1855_ = lean_box(v___x_1838_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v___x_1855_);
v___x_1857_ = v___x_1853_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_snd_1851_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
v___y_1844_ = v___x_1857_;
goto v___jp_1843_;
}
}
}
else
{
lean_object* v_snd_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1871_; 
v_snd_1861_ = lean_ctor_get(v_b_1842_, 1);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_b_1842_);
if (v_isSharedCheck_1871_ == 0)
{
lean_object* v_unused_1872_; 
v_unused_1872_ = lean_ctor_get(v_b_1842_, 0);
lean_dec(v_unused_1872_);
v___x_1863_ = v_b_1842_;
v_isShared_1864_ = v_isSharedCheck_1871_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_snd_1861_);
lean_dec(v_b_1842_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1871_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1865_ = lean_array_uget_borrowed(v_as_1839_, v_i_1840_);
lean_inc(v___x_1865_);
v___x_1866_ = lean_array_push(v_snd_1861_, v___x_1865_);
v___x_1867_ = lean_box(v___x_1848_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 1, v___x_1866_);
lean_ctor_set(v___x_1863_, 0, v___x_1867_);
v___x_1869_ = v___x_1863_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v___x_1866_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
v___y_1844_ = v___x_1869_;
goto v___jp_1843_;
}
}
}
}
else
{
return v_b_1842_;
}
v___jp_1843_:
{
size_t v___x_1845_; size_t v___x_1846_; 
v___x_1845_ = ((size_t)1ULL);
v___x_1846_ = lean_usize_add(v_i_1840_, v___x_1845_);
v_i_1840_ = v___x_1846_;
v_b_1842_ = v___y_1844_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3___boxed(lean_object* v___x_1873_, lean_object* v_as_1874_, lean_object* v_i_1875_, lean_object* v_stop_1876_, lean_object* v_b_1877_){
_start:
{
uint8_t v___x_10024__boxed_1878_; size_t v_i_boxed_1879_; size_t v_stop_boxed_1880_; lean_object* v_res_1881_; 
v___x_10024__boxed_1878_ = lean_unbox(v___x_1873_);
v_i_boxed_1879_ = lean_unbox_usize(v_i_1875_);
lean_dec(v_i_1875_);
v_stop_boxed_1880_ = lean_unbox_usize(v_stop_1876_);
lean_dec(v_stop_1876_);
v_res_1881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(v___x_10024__boxed_1878_, v_as_1874_, v_i_boxed_1879_, v_stop_boxed_1880_, v_b_1877_);
lean_dec_ref(v_as_1874_);
return v_res_1881_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__2));
v___x_1889_ = l_Lean_stringToMessageData(v___x_1888_);
return v___x_1889_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7(void){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6));
v___x_1897_ = l_Lean_stringToMessageData(v___x_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(lean_object* v_elabVal_1900_, lean_object* v_as_1901_, size_t v_i_1902_, size_t v_stop_1903_, lean_object* v_b_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_a_1909_; lean_object* v___y_1914_; uint8_t v___x_1916_; 
v___x_1916_ = lean_usize_dec_eq(v_i_1902_, v_stop_1903_);
if (v___x_1916_ == 0)
{
lean_object* v___x_1917_; lean_object* v___x_1918_; uint8_t v___x_1919_; 
v___x_1917_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1));
v___x_1918_ = lean_array_uget_borrowed(v_as_1901_, v_i_1902_);
lean_inc(v___x_1918_);
v___x_1919_ = l_Lean_Syntax_isOfKind(v___x_1918_, v___x_1917_);
if (v___x_1919_ == 0)
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec_ref(v_b_1904_);
v___x_1920_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3);
lean_inc_ref(v___y_1905_);
v___x_1921_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_1918_, v___x_1920_, v___y_1905_, v___y_1906_);
v___y_1914_ = v___x_1921_;
goto v___jp_1913_;
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; 
v___x_1922_ = lean_unsigned_to_nat(0u);
v___x_1923_ = l_Lean_Syntax_getArg(v___x_1918_, v___x_1922_);
v___x_1924_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5));
lean_inc(v___x_1923_);
v___x_1925_ = l_Lean_Syntax_isOfKind(v___x_1923_, v___x_1924_);
if (v___x_1925_ == 0)
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
lean_dec_ref(v_b_1904_);
v___x_1926_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7);
lean_inc_ref(v___y_1905_);
v___x_1927_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_1923_, v___x_1926_, v___y_1905_, v___y_1906_);
lean_dec(v___x_1923_);
v___y_1914_ = v___x_1927_;
goto v___jp_1913_;
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v_v_1930_; lean_object* v___y_1932_; lean_object* v_fst_1933_; lean_object* v_snd_1934_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1980_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; uint8_t v___x_2005_; 
v___x_1928_ = lean_unsigned_to_nat(2u);
v___x_1929_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v_v_1930_ = l_Lean_Syntax_getArg(v___x_1918_, v___x_1928_);
v___x_2001_ = l_Lean_Syntax_getArg(v___x_1923_, v___x_1922_);
v___x_2002_ = l_Lean_Syntax_getArgs(v___x_2001_);
lean_dec(v___x_2001_);
v___x_2003_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8));
v___x_2004_ = lean_array_get_size(v___x_2002_);
v___x_2005_ = lean_nat_dec_lt(v___x_1922_, v___x_2004_);
if (v___x_2005_ == 0)
{
lean_dec_ref(v___x_2002_);
v___y_1980_ = v___x_2003_;
goto v___jp_1979_;
}
else
{
lean_object* v___x_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; 
v___x_2006_ = lean_box(v___x_1925_);
v___x_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
lean_ctor_set(v___x_2007_, 1, v___x_2003_);
v___x_2008_ = lean_nat_dec_le(v___x_2004_, v___x_2004_);
if (v___x_2008_ == 0)
{
if (v___x_2005_ == 0)
{
lean_dec_ref(v___x_2007_);
lean_dec_ref(v___x_2002_);
v___y_1980_ = v___x_2003_;
goto v___jp_1979_;
}
else
{
size_t v___x_2009_; size_t v___x_2010_; lean_object* v___x_2011_; lean_object* v_snd_2012_; 
v___x_2009_ = ((size_t)0ULL);
v___x_2010_ = lean_usize_of_nat(v___x_2004_);
v___x_2011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(v___x_1925_, v___x_2002_, v___x_2009_, v___x_2010_, v___x_2007_);
lean_dec_ref(v___x_2002_);
v_snd_2012_ = lean_ctor_get(v___x_2011_, 1);
lean_inc(v_snd_2012_);
lean_dec_ref(v___x_2011_);
v___y_1980_ = v_snd_2012_;
goto v___jp_1979_;
}
}
else
{
size_t v___x_2013_; size_t v___x_2014_; lean_object* v___x_2015_; lean_object* v_snd_2016_; 
v___x_2013_ = ((size_t)0ULL);
v___x_2014_ = lean_usize_of_nat(v___x_2004_);
v___x_2015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(v___x_1925_, v___x_2002_, v___x_2013_, v___x_2014_, v___x_2007_);
lean_dec_ref(v___x_2002_);
v_snd_2016_ = lean_ctor_get(v___x_2015_, 1);
lean_inc(v_snd_2016_);
lean_dec_ref(v___x_2015_);
v___y_1980_ = v_snd_2016_;
goto v___jp_1979_;
}
}
v___jp_1931_:
{
lean_object* v___x_1935_; 
lean_inc_ref(v___y_1905_);
lean_inc(v___y_1932_);
v___x_1935_ = l_Lake_Toml_elabSimpleKey(v___y_1932_, v___y_1905_, v___y_1906_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref(v___x_1935_);
v___x_1937_ = l_Lean_Name_str___override(v_fst_1933_, v_a_1936_);
lean_inc_ref(v_snd_1934_);
lean_inc(v___x_1937_);
v___x_1938_ = l_Lake_Toml_RBDict_contains___redArg(v___x_1929_, v___x_1937_, v_snd_1934_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; 
lean_dec(v___y_1932_);
lean_inc_ref(v_elabVal_1900_);
lean_inc(v___y_1906_);
lean_inc_ref(v___y_1905_);
v___x_1939_ = lean_apply_4(v_elabVal_1900_, v_v_1930_, v___y_1905_, v___y_1906_, lean_box(0));
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref(v___x_1939_);
v___x_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1941_, 0, v_a_1940_);
v___x_1942_ = l_Lake_Toml_RBDict_push___redArg(v___x_1929_, v___x_1937_, v___x_1941_, v_snd_1934_);
v_a_1909_ = v___x_1942_;
goto v___jp_1908_;
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec(v___x_1937_);
lean_dec_ref(v_snd_1934_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec_ref(v_elabVal_1900_);
v_a_1943_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1939_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1939_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
else
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
lean_dec_ref(v_snd_1934_);
lean_dec(v_v_1930_);
v___x_1951_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2);
v___x_1952_ = l_Lean_MessageData_ofName(v___x_1937_);
v___x_1953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1951_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
v___x_1955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1953_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
lean_inc_ref(v___y_1905_);
v___x_1956_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___y_1932_, v___x_1955_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1932_);
v___y_1914_ = v___x_1956_;
goto v___jp_1913_;
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec_ref(v_snd_1934_);
lean_dec(v_fst_1933_);
lean_dec(v___y_1932_);
lean_dec(v_v_1930_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec_ref(v_elabVal_1900_);
v_a_1957_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1935_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1935_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
v___jp_1965_:
{
if (lean_obj_tag(v___y_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v_fst_1969_; lean_object* v_snd_1970_; 
v_a_1968_ = lean_ctor_get(v___y_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref(v___y_1967_);
v_fst_1969_ = lean_ctor_get(v_a_1968_, 0);
lean_inc(v_fst_1969_);
v_snd_1970_ = lean_ctor_get(v_a_1968_, 1);
lean_inc(v_snd_1970_);
lean_dec(v_a_1968_);
v___y_1932_ = v___y_1966_;
v_fst_1933_ = v_fst_1969_;
v_snd_1934_ = v_snd_1970_;
goto v___jp_1931_;
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_dec(v___y_1966_);
lean_dec(v_v_1930_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec_ref(v_elabVal_1900_);
v_a_1971_ = lean_ctor_get(v___y_1967_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___y_1967_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___y_1967_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___y_1967_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
v___jp_1979_:
{
size_t v_sz_1981_; size_t v___x_1982_; lean_object* v___x_1983_; 
v_sz_1981_ = lean_array_size(v___y_1980_);
v___x_1982_ = ((size_t)0ULL);
v___x_1983_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(v_sz_1981_, v___x_1982_, v___y_1980_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
lean_dec(v_v_1930_);
lean_dec_ref(v_b_1904_);
v___x_1984_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7);
lean_inc_ref(v___y_1905_);
v___x_1985_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_1923_, v___x_1984_, v___y_1905_, v___y_1906_);
lean_dec(v___x_1923_);
v___y_1914_ = v___x_1985_;
goto v___jp_1913_;
}
else
{
lean_object* v_val_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v_tailKey_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
lean_dec(v___x_1923_);
v_val_1986_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_val_1986_);
lean_dec_ref(v___x_1983_);
v___x_1987_ = lean_box(0);
v___x_1988_ = lean_array_get_size(v_val_1986_);
v___x_1989_ = lean_unsigned_to_nat(1u);
v___x_1990_ = lean_nat_sub(v___x_1988_, v___x_1989_);
v_tailKey_1991_ = lean_array_get(v___x_1987_, v_val_1986_, v___x_1990_);
lean_dec(v___x_1990_);
v___x_1992_ = lean_box(0);
v___x_1993_ = lean_array_pop(v_val_1986_);
v___x_1994_ = lean_array_get_size(v___x_1993_);
v___x_1995_ = lean_nat_dec_lt(v___x_1922_, v___x_1994_);
if (v___x_1995_ == 0)
{
lean_dec_ref(v___x_1993_);
v___y_1932_ = v_tailKey_1991_;
v_fst_1933_ = v___x_1992_;
v_snd_1934_ = v_b_1904_;
goto v___jp_1931_;
}
else
{
uint8_t v___x_1996_; 
v___x_1996_ = lean_nat_dec_le(v___x_1994_, v___x_1994_);
if (v___x_1996_ == 0)
{
if (v___x_1995_ == 0)
{
lean_dec_ref(v___x_1993_);
v___y_1932_ = v_tailKey_1991_;
v_fst_1933_ = v___x_1992_;
v_snd_1934_ = v_b_1904_;
goto v___jp_1931_;
}
else
{
size_t v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_usize_of_nat(v___x_1994_);
lean_inc_ref(v___y_1905_);
lean_inc_ref(v_b_1904_);
v___x_1998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_b_1904_, v___x_1925_, v___x_1993_, v___x_1982_, v___x_1997_, v___x_1992_, v_b_1904_, v___y_1905_, v___y_1906_);
lean_dec_ref(v___x_1993_);
v___y_1966_ = v_tailKey_1991_;
v___y_1967_ = v___x_1998_;
goto v___jp_1965_;
}
}
else
{
size_t v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = lean_usize_of_nat(v___x_1994_);
lean_inc_ref(v___y_1905_);
lean_inc_ref(v_b_1904_);
v___x_2000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_b_1904_, v___x_1925_, v___x_1993_, v___x_1982_, v___x_1999_, v___x_1992_, v_b_1904_, v___y_1905_, v___y_1906_);
lean_dec_ref(v___x_1993_);
v___y_1966_ = v_tailKey_1991_;
v___y_1967_ = v___x_2000_;
goto v___jp_1965_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2017_; 
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec_ref(v_elabVal_1900_);
v___x_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2017_, 0, v_b_1904_);
return v___x_2017_;
}
v___jp_1908_:
{
size_t v___x_1910_; size_t v___x_1911_; 
v___x_1910_ = ((size_t)1ULL);
v___x_1911_ = lean_usize_add(v_i_1902_, v___x_1910_);
v_i_1902_ = v___x_1911_;
v_b_1904_ = v_a_1909_;
goto _start;
}
v___jp_1913_:
{
if (lean_obj_tag(v___y_1914_) == 0)
{
lean_object* v_a_1915_; 
v_a_1915_ = lean_ctor_get(v___y_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref(v___y_1914_);
v_a_1909_ = v_a_1915_;
goto v___jp_1908_;
}
else
{
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec_ref(v_elabVal_1900_);
return v___y_1914_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___boxed(lean_object* v_elabVal_2018_, lean_object* v_as_2019_, lean_object* v_i_2020_, lean_object* v_stop_2021_, lean_object* v_b_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
size_t v_i_boxed_2026_; size_t v_stop_boxed_2027_; lean_object* v_res_2028_; 
v_i_boxed_2026_ = lean_unbox_usize(v_i_2020_);
lean_dec(v_i_2020_);
v_stop_boxed_2027_ = lean_unbox_usize(v_stop_2021_);
lean_dec(v_stop_2021_);
v_res_2028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_2018_, v_as_2019_, v_i_boxed_2026_, v_stop_boxed_2027_, v_b_2022_, v___y_2023_, v___y_2024_);
lean_dec_ref(v_as_2019_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(lean_object* v_as_2029_, size_t v_i_2030_, size_t v_stop_2031_, lean_object* v_b_2032_){
_start:
{
lean_object* v___y_2034_; uint8_t v___x_2038_; 
v___x_2038_ = lean_usize_dec_eq(v_i_2030_, v_stop_2031_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; lean_object* v_snd_2040_; 
v___x_2039_ = lean_array_uget_borrowed(v_as_2029_, v_i_2030_);
v_snd_2040_ = lean_ctor_get(v___x_2039_, 1);
if (lean_obj_tag(v_snd_2040_) == 1)
{
lean_object* v_fst_2041_; lean_object* v_val_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v_fst_2041_ = lean_ctor_get(v___x_2039_, 0);
v_val_2042_ = lean_ctor_get(v_snd_2040_, 0);
v___x_2043_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
lean_inc(v_val_2042_);
lean_inc(v_fst_2041_);
v___x_2044_ = l_Lake_Toml_RBDict_push___redArg(v___x_2043_, v_fst_2041_, v_val_2042_, v_b_2032_);
v___y_2034_ = v___x_2044_;
goto v___jp_2033_;
}
else
{
v___y_2034_ = v_b_2032_;
goto v___jp_2033_;
}
}
else
{
return v_b_2032_;
}
v___jp_2033_:
{
size_t v___x_2035_; size_t v___x_2036_; 
v___x_2035_ = ((size_t)1ULL);
v___x_2036_ = lean_usize_add(v_i_2030_, v___x_2035_);
v_i_2030_ = v___x_2036_;
v_b_2032_ = v___y_2034_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4___boxed(lean_object* v_as_2045_, lean_object* v_i_2046_, lean_object* v_stop_2047_, lean_object* v_b_2048_){
_start:
{
size_t v_i_boxed_2049_; size_t v_stop_boxed_2050_; lean_object* v_res_2051_; 
v_i_boxed_2049_ = lean_unbox_usize(v_i_2046_);
lean_dec(v_i_2046_);
v_stop_boxed_2050_ = lean_unbox_usize(v_stop_2047_);
lean_dec(v_stop_2047_);
v_res_2051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(v_as_2045_, v_i_boxed_2049_, v_stop_boxed_2050_, v_b_2048_);
lean_dec_ref(v_as_2045_);
return v_res_2051_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3(void){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__2));
v___x_2059_ = l_Lean_stringToMessageData(v___x_2058_);
return v___x_2059_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4(void){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v___x_2061_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_2060_);
return v___x_2061_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5(void){
_start:
{
lean_object* v___x_2062_; lean_object* v_t_2063_; 
v___x_2062_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v_t_2063_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_2062_);
return v_t_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(lean_object* v_x_2064_, lean_object* v_elabVal_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2069_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1));
lean_inc(v_x_2064_);
v___x_2070_ = l_Lean_Syntax_isOfKind(v_x_2064_, v___x_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
lean_dec_ref(v_elabVal_2065_);
v___x_2071_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3);
v___x_2072_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_2064_, v___x_2071_, v_a_2066_, v_a_2067_);
lean_dec(v_a_2067_);
lean_dec(v_x_2064_);
return v___x_2072_;
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v_kvs_2076_; lean_object* v_a_2078_; lean_object* v___y_2095_; lean_object* v_t_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; uint8_t v___x_2108_; 
v___x_2073_ = lean_unsigned_to_nat(0u);
v___x_2074_ = lean_unsigned_to_nat(1u);
v___x_2075_ = l_Lean_Syntax_getArg(v_x_2064_, v___x_2074_);
lean_dec(v_x_2064_);
v_kvs_2076_ = l_Lean_Syntax_getArgs(v___x_2075_);
lean_dec(v___x_2075_);
v_t_2105_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5);
v___x_2106_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_kvs_2076_);
lean_dec_ref(v_kvs_2076_);
v___x_2107_ = lean_array_get_size(v___x_2106_);
v___x_2108_ = lean_nat_dec_lt(v___x_2073_, v___x_2107_);
if (v___x_2108_ == 0)
{
lean_dec_ref(v___x_2106_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
lean_dec_ref(v_elabVal_2065_);
v_a_2078_ = v_t_2105_;
goto v___jp_2077_;
}
else
{
uint8_t v___x_2109_; 
v___x_2109_ = lean_nat_dec_le(v___x_2107_, v___x_2107_);
if (v___x_2109_ == 0)
{
if (v___x_2108_ == 0)
{
lean_dec_ref(v___x_2106_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
lean_dec_ref(v_elabVal_2065_);
v_a_2078_ = v_t_2105_;
goto v___jp_2077_;
}
else
{
size_t v___x_2110_; size_t v___x_2111_; lean_object* v___x_2112_; 
v___x_2110_ = ((size_t)0ULL);
v___x_2111_ = lean_usize_of_nat(v___x_2107_);
v___x_2112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_2065_, v___x_2106_, v___x_2110_, v___x_2111_, v_t_2105_, v_a_2066_, v_a_2067_);
lean_dec_ref(v___x_2106_);
v___y_2095_ = v___x_2112_;
goto v___jp_2094_;
}
}
else
{
size_t v___x_2113_; size_t v___x_2114_; lean_object* v___x_2115_; 
v___x_2113_ = ((size_t)0ULL);
v___x_2114_ = lean_usize_of_nat(v___x_2107_);
v___x_2115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_2065_, v___x_2106_, v___x_2113_, v___x_2114_, v_t_2105_, v_a_2066_, v_a_2067_);
lean_dec_ref(v___x_2106_);
v___y_2095_ = v___x_2115_;
goto v___jp_2094_;
}
}
v___jp_2077_:
{
lean_object* v_items_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
v_items_2079_ = lean_ctor_get(v_a_2078_, 0);
lean_inc_ref(v_items_2079_);
lean_dec_ref(v_a_2078_);
v___x_2080_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4);
v___x_2081_ = lean_array_get_size(v_items_2079_);
v___x_2082_ = lean_nat_dec_lt(v___x_2073_, v___x_2081_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; 
lean_dec_ref(v_items_2079_);
v___x_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2080_);
return v___x_2083_;
}
else
{
uint8_t v___x_2084_; 
v___x_2084_ = lean_nat_dec_le(v___x_2081_, v___x_2081_);
if (v___x_2084_ == 0)
{
if (v___x_2082_ == 0)
{
lean_object* v___x_2085_; 
lean_dec_ref(v_items_2079_);
v___x_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2080_);
return v___x_2085_;
}
else
{
size_t v___x_2086_; size_t v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2086_ = ((size_t)0ULL);
v___x_2087_ = lean_usize_of_nat(v___x_2081_);
v___x_2088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(v_items_2079_, v___x_2086_, v___x_2087_, v___x_2080_);
lean_dec_ref(v_items_2079_);
v___x_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
return v___x_2089_;
}
}
else
{
size_t v___x_2090_; size_t v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2090_ = ((size_t)0ULL);
v___x_2091_ = lean_usize_of_nat(v___x_2081_);
v___x_2092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(v_items_2079_, v___x_2090_, v___x_2091_, v___x_2080_);
lean_dec_ref(v_items_2079_);
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
return v___x_2093_;
}
}
}
v___jp_2094_:
{
if (lean_obj_tag(v___y_2095_) == 0)
{
lean_object* v_a_2096_; 
v_a_2096_ = lean_ctor_get(v___y_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref(v___y_2095_);
v_a_2078_ = v_a_2096_;
goto v___jp_2077_;
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
v_a_2097_ = lean_ctor_get(v___y_2095_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___y_2095_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___y_2095_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___y_2095_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___boxed(lean_object* v_x_2116_, lean_object* v_elabVal_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(v_x_2116_, v_elabVal_2117_, v_a_2118_, v_a_2119_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(lean_object* v_00_u03b1_2122_, lean_object* v_ref_2123_, lean_object* v_msg_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg(v_ref_2123_, v_msg_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___boxed(lean_object* v_00_u03b1_2130_, lean_object* v_ref_2131_, lean_object* v_msg_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(v_00_u03b1_2130_, v_ref_2131_, v_msg_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2133_);
lean_dec(v_ref_2131_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1(lean_object* v_00_u03b1_2138_, lean_object* v_msg_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(v_msg_2139_, v___y_2141_, v___y_2142_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2145_, lean_object* v_msg_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1(v_00_u03b1_2145_, v_msg_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec_ref(v___y_2147_);
return v_res_2151_;
}
}
static lean_object* _init_l_Lake_Toml_elabVal___closed__1(void){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = ((lean_object*)(l_Lake_Toml_elabVal___closed__0));
v___x_2154_ = l_Lean_stringToMessageData(v___x_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal___boxed(lean_object* v_x_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Lake_Toml_elabVal(v_x_2155_, v_a_2156_, v_a_2157_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal(lean_object* v_x_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_){
_start:
{
lean_object* v___x_2164_; uint8_t v___x_2165_; 
v___x_2164_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1));
lean_inc(v_x_2160_);
v___x_2165_ = l_Lean_Syntax_isOfKind(v_x_2160_, v___x_2164_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2166_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1));
lean_inc(v_x_2160_);
v___x_2167_ = l_Lean_Syntax_isOfKind(v_x_2160_, v___x_2166_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; uint8_t v___x_2169_; 
v___x_2168_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1));
lean_inc(v_x_2160_);
v___x_2169_ = l_Lean_Syntax_isOfKind(v_x_2160_, v___x_2168_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; uint8_t v___x_2171_; 
v___x_2170_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1));
lean_inc(v_x_2160_);
v___x_2171_ = l_Lean_Syntax_isOfKind(v_x_2160_, v___x_2170_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2172_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1));
lean_inc(v_x_2160_);
v___x_2173_ = l_Lean_Syntax_isOfKind(v_x_2160_, v___x_2172_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2174_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3));
lean_inc(v_x_2160_);
v___x_2175_ = l_Lean_Syntax_isOfKind(v_x_2160_, v___x_2174_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2176_; uint8_t v___x_2177_; 
v___x_2176_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1));
lean_inc(v_x_2160_);
v___x_2177_ = l_Lean_Syntax_isOfKind(v_x_2160_, v___x_2176_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; uint8_t v___x_2179_; 
v___x_2178_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3));
lean_inc(v_x_2160_);
v___x_2179_ = l_Lean_Syntax_isOfKind(v_x_2160_, v___x_2178_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; uint8_t v___x_2181_; 
v___x_2180_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1));
lean_inc(v_x_2160_);
v___x_2181_ = l_Lean_Syntax_isOfKind(v_x_2160_, v___x_2180_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2182_; uint8_t v___x_2183_; 
v___x_2182_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1));
lean_inc(v_x_2160_);
v___x_2183_ = l_Lean_Syntax_isOfKind(v_x_2160_, v___x_2182_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = lean_obj_once(&l_Lake_Toml_elabVal___closed__1, &l_Lake_Toml_elabVal___closed__1_once, _init_l_Lake_Toml_elabVal___closed__1);
v___x_2185_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_2160_, v___x_2184_, v_a_2161_, v_a_2162_);
lean_dec(v_a_2162_);
lean_dec(v_x_2160_);
return v___x_2185_;
}
else
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = lean_alloc_closure((void*)(l_Lake_Toml_elabVal___boxed), 4, 0);
lean_inc(v_x_2160_);
v___x_2187_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(v_x_2160_, v___x_2186_, v_a_2161_, v_a_2162_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2196_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2190_ = v___x_2187_;
v_isShared_2191_ = v_isSharedCheck_2196_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2187_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2196_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2192_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_2192_, 0, v_x_2160_);
lean_ctor_set(v___x_2192_, 1, v_a_2188_);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v___x_2192_);
v___x_2194_ = v___x_2190_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2192_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec(v_x_2160_);
v_a_2197_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2187_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2187_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
}
else
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = lean_alloc_closure((void*)(l_Lake_Toml_elabVal___boxed), 4, 0);
lean_inc(v_x_2160_);
v___x_2206_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(v_x_2160_, v___x_2205_, v_a_2161_, v_a_2162_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2215_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2209_ = v___x_2206_;
v_isShared_2210_ = v_isSharedCheck_2215_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2215_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2211_, 0, v_x_2160_);
lean_ctor_set(v___x_2211_, 1, v_a_2207_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2211_);
v___x_2213_ = v___x_2209_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec(v_x_2160_);
v_a_2216_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2206_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2206_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
}
else
{
lean_object* v___x_2224_; 
lean_inc(v_x_2160_);
v___x_2224_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(v_x_2160_, v_a_2161_, v_a_2162_);
lean_dec(v_a_2162_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2234_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2227_ = v___x_2224_;
v_isShared_2228_ = v_isSharedCheck_2234_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2224_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2234_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; uint8_t v___x_2230_; lean_object* v___x_2232_; 
v___x_2229_ = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(v___x_2229_, 0, v_x_2160_);
v___x_2230_ = lean_unbox(v_a_2225_);
lean_dec(v_a_2225_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*1, v___x_2230_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v___x_2229_);
v___x_2232_ = v___x_2227_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2229_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
lean_dec(v_x_2160_);
v_a_2235_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2224_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2224_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
}
else
{
lean_object* v___x_2243_; 
lean_inc(v_x_2160_);
v___x_2243_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(v_x_2160_, v_a_2161_, v_a_2162_);
lean_dec(v_a_2162_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2252_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2246_ = v___x_2243_;
v_isShared_2247_ = v_isSharedCheck_2252_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2243_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2252_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2248_; lean_object* v___x_2250_; 
v___x_2248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2248_, 0, v_x_2160_);
lean_ctor_set(v___x_2248_, 1, v_a_2244_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 0, v___x_2248_);
v___x_2250_ = v___x_2246_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_dec(v_x_2160_);
v_a_2253_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2243_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2243_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
}
else
{
lean_object* v___x_2261_; 
v___x_2261_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(v_x_2160_, v_a_2161_, v_a_2162_);
lean_dec(v_a_2162_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2270_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2264_ = v___x_2261_;
v_isShared_2265_ = v_isSharedCheck_2270_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2261_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2270_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2268_; 
v___x_2266_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2266_, 0, v_x_2160_);
lean_ctor_set(v___x_2266_, 1, v_a_2262_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v___x_2266_);
v___x_2268_ = v___x_2264_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2266_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
lean_dec(v_x_2160_);
v_a_2271_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2261_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2261_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2274_ == 0)
{
v___x_2276_ = v___x_2273_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
}
else
{
lean_object* v___x_2279_; 
v___x_2279_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(v_x_2160_, v_a_2161_, v_a_2162_);
lean_dec(v_a_2162_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2289_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2282_ = v___x_2279_;
v_isShared_2283_ = v_isSharedCheck_2289_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2279_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2289_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2287_; 
v___x_2284_ = lean_nat_to_int(v_a_2280_);
v___x_2285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2285_, 0, v_x_2160_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 0, v___x_2285_);
v___x_2287_ = v___x_2282_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec(v_x_2160_);
v_a_2290_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2279_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2279_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
}
else
{
lean_object* v___x_2298_; 
v___x_2298_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(v_x_2160_, v_a_2161_, v_a_2162_);
lean_dec(v_a_2162_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2308_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2301_ = v___x_2298_;
v_isShared_2302_ = v_isSharedCheck_2308_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2298_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2308_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2306_; 
v___x_2303_ = lean_nat_to_int(v_a_2299_);
v___x_2304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2304_, 0, v_x_2160_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v___x_2304_);
v___x_2306_ = v___x_2301_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_dec(v_x_2160_);
v_a_2309_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2298_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2298_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
else
{
lean_object* v___x_2317_; 
v___x_2317_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(v_x_2160_, v_a_2161_, v_a_2162_);
lean_dec(v_a_2162_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2327_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2320_ = v___x_2317_;
v_isShared_2321_ = v_isSharedCheck_2327_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2327_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2325_; 
v___x_2322_ = lean_nat_to_int(v_a_2318_);
v___x_2323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2323_, 0, v_x_2160_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v___x_2323_);
v___x_2325_ = v___x_2320_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_dec(v_x_2160_);
v_a_2328_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2317_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2317_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
}
else
{
lean_object* v___x_2336_; 
v___x_2336_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(v_x_2160_, v_a_2161_, v_a_2162_);
lean_dec(v_a_2162_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2345_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2345_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2345_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2341_; lean_object* v___x_2343_; 
v___x_2341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2341_, 0, v_x_2160_);
lean_ctor_set(v___x_2341_, 1, v_a_2337_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2341_);
v___x_2343_ = v___x_2339_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2341_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec(v_x_2160_);
v_a_2346_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2336_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2336_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
}
else
{
lean_object* v___x_2354_; 
v___x_2354_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(v_x_2160_, v_a_2161_, v_a_2162_);
lean_dec(v_a_2162_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2364_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2357_ = v___x_2354_;
v_isShared_2358_ = v_isSharedCheck_2364_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2354_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2364_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2359_; double v___x_2360_; lean_object* v___x_2362_; 
v___x_2359_ = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(v___x_2359_, 0, v_x_2160_);
v___x_2360_ = lean_unbox_float(v_a_2355_);
lean_dec(v_a_2355_);
lean_ctor_set_float(v___x_2359_, sizeof(void*)*1, v___x_2360_);
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v___x_2359_);
v___x_2362_ = v___x_2357_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2359_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec(v_x_2160_);
v_a_2365_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2354_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2354_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
}
}
lean_object* runtime_initialize_Lake_Toml_Data_Value(uint8_t builtin);
lean_object* runtime_initialize_Lake_Toml_Grammar(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_Elab_Value(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Toml_Data_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Toml_Grammar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Toml_Grammar(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Toml_Elab_Value(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Toml_Grammar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Toml_Data_Value(uint8_t builtin);
lean_object* initialize_Lake_Toml_Grammar(uint8_t builtin);
lean_object* initialize_Lake_Toml_Grammar(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Elab_Value(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Toml_Data_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Grammar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Grammar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Toml_Elab_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Toml_Elab_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Toml_Elab_Value(builtin);
}
#ifdef __cplusplus
}
#endif
