package services;

import javax.servlet.http.HttpSession;

public class LogoutService {

    /**
     * Performs the logout operation by invalidating the provided session.
     *
     * @param session the HttpSession to invalidate. Must not be null.
     * @throws IllegalArgumentException if the provided session is null.
     * @throws IllegalStateException    if the session is already invalidated.
     */
    public void logout(HttpSession session) {
        if (session == null) {
            throw new IllegalArgumentException("Session cannot be null when performing logout.");
        }

        // Propagates IllegalStateException if session is already invalidated,
        // ensuring the caller is aware of the invalid state usage.
        session.invalidate();
    }
}
