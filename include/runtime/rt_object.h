#ifndef _RT_OBJECT_H
#define _RT_OBJECT_H

// size = 12 bytes
struct StdString {
	/*0x00*/ UInt		unknown;
	/*0x04*/ UInt		len;
	/*0x08*/ HChar*	data;
};

struct StdVector {
	UInt	unknown;
	UInt	len;
	void*	data;
};

struct StdList {
	UInt	unknown;
	UInt	len;
	void*	data;
};

struct StdUniquePtr {
	Addr	p;
};

typedef 
struct _ObjectReference {
	Addr	reference_;
} ObjectReference;

/* The C++ mirror classes for the Java classes */
struct _ClassMirror;

/* size = 8 bytes */
typedef
struct _ObjectMirror {
	struct _ClassMirror *klass_;
	UInt			monitor_;
} ObjectMirror;

/* size = 16 bytes */
typedef
struct _StringMirror {
	ObjectMirror object_;
	Int			count_;
	UInt		hash_code_;
	UShort	value_[0];
} StringMirror;

// C++ mirror of java.lang.Class
/* size = 136 bytes */
typedef
struct _ClassMirror {
	ObjectMirror		object_;
	/*0x00*/ void*	class_loader_;
	/*0x04*/ void*	component_type_;
	/*0x08*/ void*	dex_cache_;
	/*0x0c*/ void*	dex_cache_strings_;
	/*0x10*/ void*	iftable_;
  // Descriptor for the class such as "java.lang.Class" or "[C". Lazily initialized by ComputeName
	/*0x14   struct StdString*	name_;*/
	/*0x14*/ struct StringMirror*	name_;
	/*0x18*/ struct ClassPlus*	super_class_;
	/*0x1c*/ struct ClassPlus*	verify_error_class_;
	// Virtual method table (vtable), for use by "invoke-virtual".
	/*0x20*/ void*	vtable_;
	// Access flags; low 16 bits are defined by VM spec.
	/*0x24*/ UInt		access_flags_;
	// static, private, and <init> methods. Pointer to an ArtMethod array.
	/*0x28*/ ULong	direct_methods_;
	/*0x30*/ ULong	ifields_;
	/*0x38*/ ULong	sfields_;
	// Virtual methods defined in this class: invoked through vtable. Pointer to an ArtMethod array
	/*0x40*/ ULong	virtual_methods_;
  // Total size of the Class instance; used when allocating storage on gc heap.
  // See also object_size_.
	/*0x48*/ UInt	class_size_;
	/*0x4c*/ UInt	clinit_thread_id_;
	// ClassDef index in dex file, -1 if no class definition such as an array.
	// TODO: really 16bits
	/*0x50*/ UInt	dex_class_def_idx_;
	// Type index in dex file.
	// TODO: really 16bits
	/*0x54*/ UInt	dex_type_idx_;
	// Number of derect methods
	/*0x58*/ UInt	num_direct_methods_;
	// Number of instance fields
	/*0x5c*/ UInt	num_instance_fields_;
	// Number of instance fields that are object refs.
	/*0x60*/ UInt	num_reference_instance_fields_;
	// Nmber of static fields that are object refs
	/*0x64*/ UInt	num_reference_static_fields_;
	// Number of static fields
	/*0x68*/ UInt	num_static_fields_;
	// Number of virtual methods
	/*0x6c*/ UInt	num_virtual_methods_;
  // Total object size; used when allocating storage on gc heap.
  // (For interfaces and abstract classes this will be zero.)
  // See also class_size_.
	/*0x70*/ UInt	object_size_;
	/*0x74*/ UInt	primitive_type_;
	/*0x78*/ UInt	reference_instance_offset_;
	/*0x7c*/ UInt	status_;
} ClassMirror;

/* size = *** bytes */
typedef 
struct _ArrayMirror {
	ObjectMirror object_;
	UInt		length_;
	UInt		first_element_[0];
} ArrayMirror;

typedef
struct _PrimitiveArrayMirror {
	ArrayMirror	arrary_;
} PrimitiveArrayMiror;

typedef
struct _PointerArrayMirror {
	ArrayMirror	arrary_;
} PointerArrayMirror;



#endif // _RT_OBJECT_H
