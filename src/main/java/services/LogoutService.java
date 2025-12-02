package services;

import javax.servlet.http.HttpSession;

public class LogoutService {
    public void logout(HttpSession session) {
        if (session != null) {
            session.invalidate();
        }
    }
}
