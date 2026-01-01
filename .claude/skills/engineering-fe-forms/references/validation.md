# Advanced Validation Patterns

## Common Schema Patterns

### Email Variations

```ts
// Basic email
const email = z.string().email();

// Business email (no free providers)
const businessEmail = z.string().email().refine(
  (email) => {
    const freeProviders = ["gmail.com", "yahoo.com", "hotmail.com", "outlook.com"];
    const domain = email.split("@")[1];
    return !freeProviders.includes(domain);
  },
  { message: "Please use a business email address" }
);

// Email with domain whitelist
const corporateEmail = z.string().email().refine(
  (email) => email.endsWith("@company.com"),
  { message: "Must be a company.com email" }
);
```

### Password Strength

```ts
const password = z
  .string()
  .min(8, "Minimum 8 characters")
  .regex(/[A-Z]/, "Must contain uppercase letter")
  .regex(/[a-z]/, "Must contain lowercase letter")
  .regex(/[0-9]/, "Must contain number")
  .regex(/[^A-Za-z0-9]/, "Must contain special character");

// With strength meter helper
function getPasswordStrength(password: string): number {
  let strength = 0;
  if (password.length >= 8) strength++;
  if (password.length >= 12) strength++;
  if (/[A-Z]/.test(password)) strength++;
  if (/[a-z]/.test(password)) strength++;
  if (/[0-9]/.test(password)) strength++;
  if (/[^A-Za-z0-9]/.test(password)) strength++;
  return Math.min(strength, 5); // 0-5 scale
}
```

### Phone Numbers

```ts
// Basic format
const phone = z.string().regex(
  /^\+?[1-9]\d{1,14}$/,
  "Invalid phone number"
);

// US phone
const usPhone = z.string().regex(
  /^\(?([0-9]{3})\)?[-. ]?([0-9]{3})[-. ]?([0-9]{4})$/,
  "Invalid US phone number"
);

// International with country code
const internationalPhone = z.string().regex(
  /^\+[1-9]\d{6,14}$/,
  "Use format: +1234567890"
);
```

### URLs

```ts
// Basic URL
const url = z.string().url();

// HTTPS only
const secureUrl = z.string().url().startsWith("https://", "Must be HTTPS");

// Specific domain
const githubUrl = z.string().url().refine(
  (url) => url.includes("github.com"),
  { message: "Must be a GitHub URL" }
);
```

### Dates

```ts
// Date string (YYYY-MM-DD)
const dateString = z.string().regex(/^\d{4}-\d{2}-\d{2}$/);

// Coerced Date object
const date = z.coerce.date();

// Future date only
const futureDate = z.coerce.date().refine(
  (date) => date > new Date(),
  { message: "Date must be in the future" }
);

// Date range
const dateRange = z.object({
  startDate: z.coerce.date(),
  endDate: z.coerce.date(),
}).refine(
  (data) => data.endDate > data.startDate,
  {
    message: "End date must be after start date",
    path: ["endDate"],
  }
);

// Age validation
const birthDate = z.coerce.date().refine(
  (date) => {
    const age = Math.floor(
      (Date.now() - date.getTime()) / (365.25 * 24 * 60 * 60 * 1000)
    );
    return age >= 18;
  },
  { message: "Must be at least 18 years old" }
);
```

### Currency

```ts
// Dollar amount
const amount = z
  .string()
  .regex(/^\d+(\.\d{1,2})?$/, "Invalid amount")
  .transform((val) => parseFloat(val));

// With min/max
const price = z.coerce.number()
  .positive("Must be positive")
  .max(10000, "Maximum $10,000");
```

## Conditional Schemas

### Union Types

```ts
const paymentSchema = z.discriminatedUnion("method", [
  z.object({
    method: z.literal("card"),
    cardNumber: z.string().length(16),
    expiryDate: z.string().regex(/^\d{2}\/\d{2}$/),
    cvv: z.string().length(3),
  }),
  z.object({
    method: z.literal("bank"),
    accountNumber: z.string().min(8),
    routingNumber: z.string().length(9),
  }),
  z.object({
    method: z.literal("paypal"),
    paypalEmail: z.string().email(),
  }),
]);

type Payment = z.infer<typeof paymentSchema>;
```

### Optional Fields Based on Others

```ts
const schema = z.object({
  accountType: z.enum(["personal", "business"]),
  firstName: z.string().min(1),
  lastName: z.string().min(1),
  companyName: z.string().optional(),
  taxId: z.string().optional(),
}).superRefine((data, ctx) => {
  if (data.accountType === "business") {
    if (!data.companyName) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        message: "Company name required for business accounts",
        path: ["companyName"],
      });
    }
    if (!data.taxId) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        message: "Tax ID required for business accounts",
        path: ["taxId"],
      });
    }
  }
});
```

## Async Validation

### Email Availability Check

```ts
const signupSchema = z.object({
  email: z.string().email(),
  password: z.string().min(8),
}).refine(
  async (data) => {
    const response = await fetch(`/api/check-email?email=${data.email}`);
    const { available } = await response.json();
    return available;
  },
  {
    message: "Email already registered",
    path: ["email"],
  }
);

// Usage with React Hook Form
const form = useForm({
  resolver: zodResolver(signupSchema),
  mode: "onBlur", // Validate on blur for async
});
```

### Username Availability

```ts
const usernameSchema = z
  .string()
  .min(3, "At least 3 characters")
  .max(20, "Maximum 20 characters")
  .regex(/^[a-zA-Z0-9_]+$/, "Only letters, numbers, underscores")
  .refine(
    async (username) => {
      // Debounce this in the UI
      const response = await fetch(`/api/check-username?username=${username}`);
      return response.ok;
    },
    { message: "Username taken" }
  );
```

## Array Validation

### Array of Objects

```ts
const teamSchema = z.object({
  name: z.string().min(1),
  members: z.array(
    z.object({
      email: z.string().email(),
      role: z.enum(["admin", "member", "viewer"]),
    })
  ).min(1, "At least one member required"),
});
```

### Unique Values in Array

```ts
const tagsSchema = z
  .array(z.string())
  .refine(
    (tags) => new Set(tags).size === tags.length,
    { message: "Tags must be unique" }
  );
```

### Array with Constraints

```ts
const imagesSchema = z
  .array(z.instanceof(File))
  .min(1, "Upload at least one image")
  .max(5, "Maximum 5 images")
  .refine(
    (files) => files.every((file) => file.size <= 5 * 1024 * 1024),
    { message: "Each file must be under 5MB" }
  )
  .refine(
    (files) => files.every((file) => file.type.startsWith("image/")),
    { message: "Only image files allowed" }
  );
```

## Transform and Preprocess

### Sanitize Input

```ts
const schema = z.object({
  name: z.string().transform((val) => val.trim()),
  email: z.string().email().transform((val) => val.toLowerCase()),
  phone: z.string().transform((val) => val.replace(/\D/g, "")),
});
```

### Parse Numeric Strings

```ts
const schema = z.object({
  quantity: z.preprocess(
    (val) => (val === "" ? undefined : Number(val)),
    z.number().positive().optional()
  ),
  price: z.coerce.number().positive(),
});
```

### Default Values

```ts
const schema = z.object({
  name: z.string().min(1),
  status: z.enum(["draft", "published"]).default("draft"),
  tags: z.array(z.string()).default([]),
  createdAt: z.date().default(() => new Date()),
});
```

## Schema Composition

### Extend Schema

```ts
const baseUserSchema = z.object({
  email: z.string().email(),
  name: z.string().min(1),
});

const createUserSchema = baseUserSchema.extend({
  password: z.string().min(8),
});

const updateUserSchema = baseUserSchema.partial();

const adminUserSchema = baseUserSchema.extend({
  role: z.literal("admin"),
  permissions: z.array(z.string()),
});
```

### Merge Schemas

```ts
const addressSchema = z.object({
  street: z.string(),
  city: z.string(),
  country: z.string(),
});

const contactSchema = z.object({
  email: z.string().email(),
  phone: z.string(),
});

const fullProfileSchema = addressSchema.merge(contactSchema);
```

### Pick and Omit

```ts
const fullSchema = z.object({
  id: z.string(),
  email: z.string().email(),
  password: z.string(),
  name: z.string(),
  createdAt: z.date(),
});

// Create form (no id, createdAt)
const createSchema = fullSchema.omit({ id: true, createdAt: true });

// Update email only
const updateEmailSchema = fullSchema.pick({ email: true });
```

## Error Customization

### Custom Error Messages

```ts
const schema = z.object({
  age: z.number({
    required_error: "Age is required",
    invalid_type_error: "Age must be a number",
  }).min(18, { message: "Must be at least 18" }),
});
```

### Custom Error Map

```ts
const customErrorMap: z.ZodErrorMap = (issue, ctx) => {
  if (issue.code === z.ZodIssueCode.invalid_type) {
    if (issue.expected === "string") {
      return { message: "This field is required" };
    }
  }
  if (issue.code === z.ZodIssueCode.too_small) {
    return { message: `Minimum ${issue.minimum} characters` };
  }
  return { message: ctx.defaultError };
};

z.setErrorMap(customErrorMap);
```

### Localized Errors

```ts
const createLocalizedSchema = (t: (key: string) => string) =>
  z.object({
    email: z.string().email(t("validation.email.invalid")),
    password: z.string().min(8, t("validation.password.min")),
  });
```

## Form-Specific Patterns

### Debounced Async Validation

```tsx
"use client";

import { useDebouncedCallback } from "use-debounce";

export function UsernameInput() {
  const { register, setError, clearErrors } = useFormContext();
  const [isChecking, setIsChecking] = useState(false);

  const checkUsername = useDebouncedCallback(async (value: string) => {
    if (value.length < 3) return;
    
    setIsChecking(true);
    const available = await checkUsernameAvailability(value);
    setIsChecking(false);

    if (!available) {
      setError("username", { message: "Username taken" });
    } else {
      clearErrors("username");
    }
  }, 500);

  return (
    <FormInput
      {...register("username", {
        onChange: (e) => checkUsername(e.target.value),
      })}
      label="Username"
      suffix={isChecking && <Spinner className="size-4" />}
    />
  );
}
```

### Dependent Field Validation

```tsx
"use client";

import { useWatch } from "react-hook-form";

export function ConfirmPasswordField() {
  const { register, formState: { errors } } = useFormContext();
  const password = useWatch({ name: "password" });

  return (
    <FormInput
      {...register("confirmPassword", {
        validate: (value) =>
          value === password || "Passwords don't match",
      })}
      label="Confirm Password"
      type="password"
      error={errors.confirmPassword?.message as string}
    />
  );
}
```