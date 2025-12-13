package services;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

import javax.servlet.http.HttpSession;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

@ExtendWith(MockitoExtension.class)
class LogoutServiceTest {

    @Mock
    private HttpSession session;

    @InjectMocks
    private LogoutService logoutService;

    // =================================================================================================
    // logout Tests
    // =================================================================================================

    @Test
    @DisplayName("TF1: Should throw exception when Session is null")
    void shouldThrowExceptionWhenSessionIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> logoutService.logout(null));
        assertEquals("Session cannot be null when performing logout.", exception.getMessage());
    }

    @Test
    @DisplayName("TF2: Should invalidate session when Session is active")
    void shouldInvalidateSessionWhenSessionIsActive() {
        // Act
        logoutService.logout(session);

        // Assert
        verify(session).invalidate();
    }

    @Test
    @DisplayName("TF3: Should throw exception when Session is already invalidated")
    void shouldThrowExceptionWhenSessionIsAlreadyInvalidated() {
        // Arrange
        doThrow(new IllegalStateException("Session already invalidated"))
                .when(session).invalidate();

        // Act & Assert
        IllegalStateException exception = assertThrows(
                IllegalStateException.class,
                () -> logoutService.logout(session));
        assertEquals("Session already invalidated", exception.getMessage());

        verify(session).invalidate();
    }
}
