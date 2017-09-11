package com.empowerops.babel;

/**
 * Created by Justin Casol on 1/14/2015.
 */
public class UnimplementedBuiltInIdentifierException extends UnsupportedOperationException {
    public UnimplementedBuiltInIdentifierException() {
        super();
    }

    public UnimplementedBuiltInIdentifierException(String message) {
        super(message);
    }

    public UnimplementedBuiltInIdentifierException(String message, Throwable cause) {
        super(message, cause);
    }

    public UnimplementedBuiltInIdentifierException(Throwable cause) {
        super(cause);
    }
}
