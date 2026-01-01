---
name: frontend-forms
description: Form handling with React Hook Form and Zod validation for Next.js applications. Covers schema definition, field-level and form-level validation, error display, multi-step forms, file uploads, and server action integration. Triggers on: form implementation, validation logic, React Hook Form setup, Zod schemas, form submission, multi-step wizards, file upload forms.
---

# Frontend Forms

Implement robust form handling with React Hook Form and Zod.

## Setup

```bash
npm install react-hook-form @hookform/resolvers zod
```

## Core Pattern

```tsx
"use client";

import { useForm } from "react-hook-form";
import { zodResolver } from "@hookform/resolvers/zod";
import { z } from "zod";

// 1. Define schema
const schema = z.object({
  email: z.string().email("Invalid email address"),
  password: z.string().min(8, "Password must be at least 8 characters"),
});

type FormData = z.infer<typeof schema>;

// 2. Create form component
export function LoginForm() {
  const {
    register,
    handleSubmit,
    formState: { errors, isSubmitting },
  } = useForm<FormData>({
    resolver: zodResolver(schema),
  });

  // 3. Handle submission
  const onSubmit = async (data: FormData) => {
    const result = await loginAction(data);
    if (result.error) {
      // Handle error
    }
  };

  return (
    <form onSubmit={handleSubmit(onSubmit)}>
      <Input
        {...register("email")}
        label="Email"
        error={errors.email?.message}
      />
      <Input
        {...register("password")}
        type="password"
        label="Password"
        error={errors.password?.message}
      />
      <Button type="submit" isDisabled={isSubmitting}>
        {isSubmitting ? "Signing in..." : "Sign in"}
      </Button>
    </form>
  );
}
```

## Zod Schema Patterns

### Basic Types

```ts
const schema = z.object({
  // Strings
  name: z.string().min(1, "Required"),
  email: z.string().email(),
  url: z.string().url().optional(),
  
  // Numbers
  age: z.coerce.number().min(0).max(120),  // coerce from string input
  price: z.coerce.number().positive(),
  
  // Booleans
  terms: z.literal(true, { errorMap: () => ({ message: "Must accept terms" }) }),
  subscribe: z.boolean().default(false),
  
  // Enums
  role: z.enum(["admin", "user", "guest"]),
  status: z.enum(["active", "inactive"]).default("active"),
  
  // Dates
  startDate: z.coerce.date(),
  birthDate: z.string().regex(/^\d{4}-\d{2}-\d{2}$/, "Use YYYY-MM-DD format"),
  
  // Arrays
  tags: z.array(z.string()).min(1, "Select at least one tag"),
  
  // Optional with default
  count: z.coerce.number().default(0),
});
```

### Conditional Validation

```ts
const schema = z.object({
  hasCompany: z.boolean(),
  companyName: z.string().optional(),
}).refine(
  (data) => !data.hasCompany || (data.hasCompany && data.companyName),
  {
    message: "Company name required when has company is checked",
    path: ["companyName"],
  }
);
```

### Cross-Field Validation

```ts
const schema = z.object({
  password: z.string().min(8),
  confirmPassword: z.string(),
}).refine((data) => data.password === data.confirmPassword, {
  message: "Passwords don't match",
  path: ["confirmPassword"],
});
```

### Complex Validation

```ts
const schema = z.object({
  email: z.string().email(),
}).refine(
  async (data) => {
    // Async validation (e.g., check if email exists)
    const exists = await checkEmailExists(data.email);
    return !exists;
  },
  {
    message: "Email already registered",
    path: ["email"],
  }
);
```

## Form Component Integration

### Input Wrapper

```tsx
// components/form/FormInput.tsx
"use client";

import { Input } from "@/components/ui/Input";
import { forwardRef } from "react";
import type { InputProps } from "@/components/ui/Input";

interface FormInputProps extends InputProps {
  label: string;
  error?: string;
  hint?: string;
}

export const FormInput = forwardRef<HTMLInputElement, FormInputProps>(
  ({ label, error, hint, ...props }, ref) => {
    return (
      <div className="space-y-1.5">
        <label className="text-sm font-medium text-primary">
          {label}
          {props.required && <span className="text-error-primary ml-0.5">*</span>}
        </label>
        <Input ref={ref} {...props} aria-invalid={!!error} />
        {error && (
          <p className="text-sm text-error-primary">{error}</p>
        )}
        {hint && !error && (
          <p className="text-sm text-tertiary">{hint}</p>
        )}
      </div>
    );
  }
);

FormInput.displayName = "FormInput";
```

### Select Wrapper

```tsx
// components/form/FormSelect.tsx
"use client";

import { Select, SelectItem } from "@/components/ui/Select";
import { Controller, useFormContext } from "react-hook-form";

interface FormSelectProps {
  name: string;
  label: string;
  options: { value: string; label: string }[];
  error?: string;
}

export function FormSelect({ name, label, options, error }: FormSelectProps) {
  const { control } = useFormContext();

  return (
    <div className="space-y-1.5">
      <label className="text-sm font-medium text-primary">{label}</label>
      <Controller
        name={name}
        control={control}
        render={({ field }) => (
          <Select
            selectedKey={field.value}
            onSelectionChange={field.onChange}
            aria-invalid={!!error}
          >
            {options.map((opt) => (
              <SelectItem key={opt.value} id={opt.value}>
                {opt.label}
              </SelectItem>
            ))}
          </Select>
        )}
      />
      {error && <p className="text-sm text-error-primary">{error}</p>}
    </div>
  );
}
```

## Server Action Integration

### Action Definition

```ts
// app/actions/auth.ts
"use server";

import { z } from "zod";
import { redirect } from "next/navigation";

const loginSchema = z.object({
  email: z.string().email(),
  password: z.string().min(8),
});

export type LoginState = {
  error?: string;
  fieldErrors?: Record<string, string[]>;
};

export async function loginAction(
  prevState: LoginState,
  formData: FormData
): Promise<LoginState> {
  const rawData = Object.fromEntries(formData);
  const result = loginSchema.safeParse(rawData);

  if (!result.success) {
    return {
      fieldErrors: result.error.flatten().fieldErrors,
    };
  }

  try {
    await signIn(result.data);
    redirect("/dashboard");
  } catch (error) {
    return { error: "Invalid credentials" };
  }
}
```

### Form with useActionState

```tsx
"use client";

import { useActionState } from "react";
import { loginAction, type LoginState } from "@/app/actions/auth";

export function LoginForm() {
  const [state, formAction, isPending] = useActionState<LoginState, FormData>(
    loginAction,
    {}
  );

  return (
    <form action={formAction}>
      {state.error && (
        <Alert type="error">{state.error}</Alert>
      )}

      <FormInput
        name="email"
        label="Email"
        type="email"
        error={state.fieldErrors?.email?.[0]}
      />
      <FormInput
        name="password"
        label="Password"
        type="password"
        error={state.fieldErrors?.password?.[0]}
      />

      <Button type="submit" isDisabled={isPending}>
        {isPending ? "Signing in..." : "Sign in"}
      </Button>
    </form>
  );
}
```

### Hybrid: RHF + Server Action

```tsx
"use client";

import { useForm } from "react-hook-form";
import { zodResolver } from "@hookform/resolvers/zod";
import { useTransition } from "react";
import { createProject } from "@/app/actions/projects";

export function CreateProjectForm() {
  const [isPending, startTransition] = useTransition();
  const form = useForm<FormData>({
    resolver: zodResolver(schema),
  });

  const onSubmit = (data: FormData) => {
    startTransition(async () => {
      const result = await createProject(data);
      if (result.error) {
        form.setError("root", { message: result.error });
      }
    });
  };

  return (
    <form onSubmit={form.handleSubmit(onSubmit)}>
      {form.formState.errors.root && (
        <Alert type="error">{form.formState.errors.root.message}</Alert>
      )}
      {/* fields */}
    </form>
  );
}
```

## Multi-Step Forms

### Step Controller

```tsx
"use client";

import { useState } from "react";
import { FormProvider, useForm } from "react-hook-form";
import { zodResolver } from "@hookform/resolvers/zod";

const schemas = {
  step1: z.object({
    name: z.string().min(1),
    email: z.string().email(),
  }),
  step2: z.object({
    company: z.string().min(1),
    role: z.enum(["developer", "designer", "manager"]),
  }),
  step3: z.object({
    plan: z.enum(["free", "pro", "enterprise"]),
    terms: z.literal(true),
  }),
};

const fullSchema = z.object({
  ...schemas.step1.shape,
  ...schemas.step2.shape,
  ...schemas.step3.shape,
});

type FormData = z.infer<typeof fullSchema>;

export function OnboardingWizard() {
  const [step, setStep] = useState(1);
  const methods = useForm<FormData>({
    resolver: zodResolver(fullSchema),
    mode: "onChange",
  });

  const validateStep = async () => {
    const currentSchema = schemas[`step${step}` as keyof typeof schemas];
    const fields = Object.keys(currentSchema.shape) as (keyof FormData)[];
    const isValid = await methods.trigger(fields);
    return isValid;
  };

  const nextStep = async () => {
    if (await validateStep()) {
      setStep((s) => Math.min(s + 1, 3));
    }
  };

  const prevStep = () => setStep((s) => Math.max(s - 1, 1));

  const onSubmit = async (data: FormData) => {
    await submitOnboarding(data);
  };

  return (
    <FormProvider {...methods}>
      <form onSubmit={methods.handleSubmit(onSubmit)}>
        <ProgressSteps currentStep={step} totalSteps={3} />

        {step === 1 && <Step1 />}
        {step === 2 && <Step2 />}
        {step === 3 && <Step3 />}

        <div className="flex justify-between mt-6">
          {step > 1 && (
            <Button type="button" hierarchy="secondary" onPress={prevStep}>
              Back
            </Button>
          )}
          {step < 3 ? (
            <Button type="button" onPress={nextStep}>
              Continue
            </Button>
          ) : (
            <Button type="submit" isDisabled={methods.formState.isSubmitting}>
              Complete
            </Button>
          )}
        </div>
      </form>
    </FormProvider>
  );
}
```

### Step Components

```tsx
// Step1.tsx
"use client";

import { useFormContext } from "react-hook-form";

export function Step1() {
  const { register, formState: { errors } } = useFormContext();

  return (
    <div className="space-y-4">
      <FormInput
        {...register("name")}
        label="Full Name"
        error={errors.name?.message as string}
      />
      <FormInput
        {...register("email")}
        label="Email"
        type="email"
        error={errors.email?.message as string}
      />
    </div>
  );
}
```

## File Uploads

### Schema with File Validation

```ts
const MAX_FILE_SIZE = 5 * 1024 * 1024; // 5MB
const ACCEPTED_TYPES = ["image/jpeg", "image/png", "image/webp"];

const schema = z.object({
  avatar: z
    .instanceof(File)
    .refine((file) => file.size <= MAX_FILE_SIZE, "Max file size is 5MB")
    .refine(
      (file) => ACCEPTED_TYPES.includes(file.type),
      "Only .jpg, .png, .webp formats are supported"
    )
    .optional(),
});
```

### File Input Component

```tsx
"use client";

import { useController, useFormContext } from "react-hook-form";
import { FileUploader } from "@/components/ui/FileUploader";

interface FormFileUploadProps {
  name: string;
  label: string;
  accept?: string;
  maxSize?: number;
}

export function FormFileUpload({ name, label, accept, maxSize }: FormFileUploadProps) {
  const { control, formState: { errors } } = useFormContext();
  const { field } = useController({ name, control });
  const error = errors[name]?.message as string | undefined;

  return (
    <div className="space-y-1.5">
      <label className="text-sm font-medium text-primary">{label}</label>
      <FileUploader
        onSelect={(files) => field.onChange(files[0])}
        accept={accept}
        maxSize={maxSize}
      />
      {error && <p className="text-sm text-error-primary">{error}</p>}
    </div>
  );
}
```

### Upload with Preview

```tsx
"use client";

import { useState } from "react";
import { useFormContext, useWatch } from "react-hook-form";
import { XClose } from "@untitledui/icons";

export function AvatarUpload() {
  const { control, setValue } = useFormContext();
  const file = useWatch({ control, name: "avatar" });
  const [preview, setPreview] = useState<string | null>(null);

  const handleSelect = (selectedFile: File) => {
    setValue("avatar", selectedFile);
    const url = URL.createObjectURL(selectedFile);
    setPreview(url);
  };

  const handleRemove = () => {
    setValue("avatar", undefined);
    if (preview) URL.revokeObjectURL(preview);
    setPreview(null);
  };

  return (
    <div>
      {preview ? (
        <div className="relative w-24 h-24">
          <img
            src={preview}
            alt="Preview"
            className="w-full h-full object-cover rounded-full"
          />
          <button
            type="button"
            onClick={handleRemove}
            className="absolute -top-1 -right-1 p-1 bg-primary rounded-full shadow-md"
          >
            <XClose className="size-4" />
          </button>
        </div>
      ) : (
        <FileUploader onSelect={(files) => handleSelect(files[0])} accept="image/*" />
      )}
    </div>
  );
}
```

## Error Display Patterns

### Field-Level Errors

```tsx
<FormInput
  {...register("email")}
  label="Email"
  error={errors.email?.message}  // Shows under field
/>
```

### Form-Level Errors

```tsx
{form.formState.errors.root && (
  <Alert type="error" title="Submission Failed">
    {form.formState.errors.root.message}
  </Alert>
)}
```

### Error Summary

```tsx
function ErrorSummary({ errors }: { errors: FieldErrors }) {
  const errorMessages = Object.entries(errors)
    .filter(([key]) => key !== "root")
    .map(([key, error]) => ({
      field: key,
      message: error?.message as string,
    }));

  if (errorMessages.length === 0) return null;

  return (
    <Alert type="error" title="Please fix the following errors:">
      <ul className="list-disc list-inside">
        {errorMessages.map(({ field, message }) => (
          <li key={field}>{message}</li>
        ))}
      </ul>
    </Alert>
  );
}
```

## Form File Structure

```
src/
├─ components/form/
│   ├─ FormInput.tsx
│   ├─ FormSelect.tsx
│   ├─ FormCheckbox.tsx
│   ├─ FormFileUpload.tsx
│   └─ index.ts
├─ lib/schemas/
│   ├─ auth.ts           # Login, signup schemas
│   ├─ project.ts        # Project CRUD schemas
│   └─ user.ts           # Profile, settings schemas
└─ app/actions/
    ├─ auth.ts           # Auth server actions
    └─ projects.ts       # Project server actions
```

## References

- **Validation patterns**: See [references/validation.md](references/validation.md) for advanced Zod patterns
- **Integration**: Coordinates with `frontend-data` for mutations, `untitled-ui` for form UI components